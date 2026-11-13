/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR2

@[expose] public section

/-!
# BL's round on the machine, R2 PLAYPT in mode `run`, the gauge

The gauge `π(X') = max(0, max_i α̃_i·X'/β̃_i)` over the kept rows, by one pass over the input rows `r < m`: row `r` is
read from its cells and cleared (`XV.inRow`: `â_r = a_r Π_r`, `b̂_r D_S = b_r Π_r D_S` with `Π_r` the product of the
row's denominators), then `g_N = â_r·y` and `g_D = (b̂_r D_S - â_r·μ̂_S) D_X` (`y = Â_S X̂`, R2's point), and the pair
`(b_N, b_D)` is replaced by `(g_N, g_D)` when `g_D > 0` and `b_N g_D < g_N b_D` (`bestG`). A kept row has `g_D > 0`
in mode `run` and `g_N/g_D = α̃·X'/β̃`; a dropped row has `g_N = 0`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-! ## The running maximum -/

/-- The running maximum of the fractions `num k / den k` over the rows `k < r` with `den k > 0`, from `0/1`, by cross
multiplication. -/
def bestG (num den : ℕ → ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | k + 1 => if 0 < den k ∧ (bestG num den k).1 * den k < num k * (bestG num den k).2 then (num k, den k)
    else bestG num den k

/-- The cleared entry `j` of the input row `r`: `Nm r j (Π_r / Dn r j)`, `Π_r = ∏_{j ≤ d} Dn r j`. -/
def rowA (Nm Dn : ℕ → ℕ → ℤ) (d r j : ℕ) : ℤ := Nm r j * ((∏ j' ∈ Finset.range (d + 1), Dn r j') / Dn r j)

/-- The numerator `â_r·y` of row `r`. -/
def gNI (Nm Dn : ℕ → ℕ → ℤ) (y : Fin d → ℤ) (r : ℕ) : ℤ := (fun j : Fin d => rowA Nm Dn d r j) ⬝ᵥ y

/-- The denominator `(b̂_r D_S - â_r·μ̂_S) D_X` of row `r`. -/
def gDI (Nm Dn : ℕ → ℕ → ℤ) (muS : Fin d → ℤ) (DS DX : ℤ) (r : ℕ) : ℤ :=
  (rowA Nm Dn d r d * DS - (fun j : Fin d => rowA Nm Dn d r j) ⬝ᵥ muS) * DX

theorem rowA_abs {Nm Dn : ℕ → ℕ → ℤ} {Mh : ℤ} {r : ℕ} (hM1 : 1 ≤ Mh) (hNm : ∀ j ≤ d, |Nm r j| ≤ Mh)
    (hDn : ∀ j ≤ d, 1 ≤ Dn r j ∧ Dn r j ≤ Mh) {j : ℕ} (hj : j ≤ d) : |rowA Nm Dn d r j| ≤ Mh ^ (d + 2) := by
  obtain ⟨p1, p2⟩ := prod_range_abs_le (Dn r) Mh hM1 (d + 1) (fun j hj => hDn j (by omega))
  have hq0 : 0 ≤ (∏ j' ∈ Finset.range (d + 1), Dn r j') / Dn r j := Int.ediv_nonneg (by omega) (by
    have := (hDn j hj).1; omega)
  have hq1 : (∏ j' ∈ Finset.range (d + 1), Dn r j') / Dn r j ≤ ∏ j' ∈ Finset.range (d + 1), Dn r j' :=
    Int.ediv_le_self _ (by omega)
  unfold rowA
  rw [abs_mul, abs_of_nonneg hq0, pow_succ']
  exact mul_le_mul (hNm j hj) (hq1.trans p2) hq0 (by omega)

/-! ## Conditionals on slots with an empty branch -/

section Rules

variable {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ}

theorem XV.ifS_skip (hL : LayOK L d ℓa) {x y : ℕ} {c : XCmd} {σ : Env d} {K : ℕ} {P : Env d → Prop}
    (hx : x < L.NS) (hy : y < L.NS) (hvx : |σ.sc x| < 2 ^ ℓ) (hvy : |σ.sc y| < 2 ^ ℓ)
    (ht : σ.sc x < σ.sc y → XRunsB L X ℓa ℓ c σ K P) (hf : ¬ σ.sc x < σ.sc y → P σ) :
    XRunsB L X ℓa ℓ (xifS L x y c .skip) σ (K + 2) P := by
  by_cases h : σ.sc x < σ.sc y
  · exact XV.mono (XV.ifS_t hL hx hy hvx hvy h (ht h)) (by omega) fun _ h => h
  · exact XV.mono (XV.ifS_f hL hx hy hvx hvy h (XV.skip σ)) (by omega) fun σ' e => e ▸ hf h

end Rules

/-! ## The code -/

/-- `g_D = (sRB - sTa) sDX`. -/
def ieGD : IE := .op .mul (.op .sub (.sc sRB) (.sc sTa)) (.sc sDX)

theorem ieGD_facts : ieGD.units = 5 ∧ ieGD.scr = 4 ∧ topL ieGD = (2, 1) := ⟨rfl, rfl, by
  simp [ieGD, topL, magL]⟩

/-- The update of the running maximum. -/
def xR2upd (L : Layout) : XCmd :=
  xifS L sZ sGD (.seq (toX (VL.sop2 L .mul sC1 sBN sGD)) (.seq (toX (VL.sop2 L .mul sC2 sGN sBD))
    (xifS L sC1 sC2 (.seq (toX (VL.sop2 L .add sBN sGN sZ)) (toX (VL.sop2 L .add sBD sGD sZ))) .skip))) .skip

/-- One input row. -/
def xR2row (L : Layout) : XCmd :=
  .seq (xinRow L sRD sRT sRN sRQ sRB sDS aRw rI rTT rjj rD rD1 rK rOne)
  (.seq (xdot L sZ sGN tR aRw aYv rr rk rD rOne)
  (.seq (xdot L sZ sTa tR aRw aMuS rr rk rD rOne)
  (.seq (ieGD.code L sZ sGD tR) (xR2upd L))))

/-- The gauge: `b_N := 0`, `b_D := 1`, `rD1 := d + 1`, then the rows. -/
def xR2g (L : Layout) : XCmd :=
  .seq (toX (VL.sop2 L .add sBN sZ sZ)) (.seq (toX (VL.sconst L sBD 1))
  (.seq (.prim (.frag (.nadd rD1 rD rOne))) (xforN rK rM rOne (xR2row L))))

/-- The units of `xR2g`. -/
def r2gUnits (d m : ℕ) : ℕ := 1 + (1 + (1 + (m * ((18 * d + 28) + ((d * 10 + 5) + ((d * 10 + 5) + (5 + 8)))
  + 3) + 3)))

/-- The cells the gauge changes. -/
def SG (y : ℕ) : Prop := (sBN ≤ y ∧ y ≤ sRQ) ∨ tR ≤ y
def NG (j : ℕ) : Prop := rD1 ≤ j ∧ j ≤ rk
def AG (a _k : ℕ) : Prop := a = aRw

/-- The registers one row changes: the gauge's but the row counter. -/
def NGr (j : ℕ) : Prop := rI ≤ j ∧ j ≤ rk

/-- `omega` after unfolding the cell names in the goal only (the layout bounds normalized beforehand). -/
macro "qomega" : tactic => `(tactic| ((try simp only [rD, rM, rMk, rOne, rP, rPF, rNb, rB, nN0, sZ, sMode, sFirst,
  sN, s2p, s2pF, s2g, sNe, sLam, sRint, s2eh, sEps, sLamb, sEta, sRho, sKapc, sNu, sR, sSb, sW, sA0, sB0, sDS, sDmu,
  sK, sL, nSP, nS0, aMuS, aAS, aC, aMu, aA, aB, ab, aG, nAP, nA0, sEl, aEH, aEg, aEP, aEf, oE, rEE, aWE, rJ, rT, rD2,
  sZeta, aGam, oBM, rD1, rK, rI, rTT, rjj, ri, rr, rk, sDX, sPtN, sPtD, sBN, sBD, sGN, sGD, sC1, sC2, sTa, sRB, sRD,
  sRT, sRN, sRQ, sAcc, tR, aWv, aXh, aYv, aPl, aRw, SR2, NR2, AR2, SG, NG, NGr, AG, ne_eq, not_or, not_and,
  not_not]) <;> omega))

theorem scS (σ : Env d) (x : ℕ) (v : ℝ) : (σ.setSc x v).sc x = v := by simp

theorem scO (σ : Env d) {x y : ℕ} (h : y ≠ x) (v : ℝ) : (σ.setSc x v).sc y = σ.sc y := by
  simp [Env.setSc_sc, h]

theorem incS_row : ∀ y, (y = sRD ∨ y = sRT ∨ y = sRN ∨ y = sRQ ∨ y = sRB) → SG y := by
  intro y h; simp only [SG, sRD, sRT, sRN, sRQ, sRB, sBN, tR] at *; omega
theorem incN_row : ∀ j, (j = rI ∨ j = rTT ∨ j = rjj) → NGr j := by
  intro j h; simp only [NGr, rI, rTT, rjj, rk] at *; omega
theorem incS_x {x : ℕ} (hx : sBN ≤ x ∧ x ≤ sRQ) : ∀ y, (y = x ∨ tR ≤ y) → SG y := by
  intro y h; simp only [SG] at *; omega
theorem incN_dot : ∀ j, (j = rk ∨ j = rr) → NGr j := by
  intro j h; simp only [NGr, rI, rr, rk] at *; omega
theorem incN_g : ∀ j, NGr j → NG j := by intro j h; simp only [NGr, NG, rI, rk, rD1] at *; omega

/-! ## One row -/

/-- The exponent of the gauge's pairs. -/
def tG (d E : ℕ) : ℕ := E * d + 10 * E + 2

theorem pow_mono_z {a b : ℕ} (h : a ≤ b) : (2 : ℤ) ^ a ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) h

set_option maxHeartbeats 4000000 in
/-- **One input row of the gauge**: row `r` cleared, `g_N`, `g_D`, and the running pair updated as `bestG`. -/
theorem XV.r2row {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {E m r : ℕ} {Nm Dn : ℕ → ℕ → ℤ} {Mh DS DX bN bD : ℤ} {yv muS : Fin d → ℤ} (hr : r < m)
    (hD : σ.nat rD = d) (hD1 : σ.nat rD1 = d + 1) (hK : σ.nat rK = r) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hDS : σ.sc sDS = DS) (hDX : σ.sc sDX = DX) (hy : ∀ k : Fin d, σ.arr aYv k = yv k)
    (hmu : ∀ k : Fin d, σ.arr aMuS k = muS k) (hbN : σ.sc sBN = bN) (hbD : σ.sc sBD = bD)
    (hoff : 3 + 2 * ((d + 1) * m) ≤ X.off) (hma : 4 + 2 * ((d + 1) * m) < 2 ^ ℓa)
    (hinpN : ∀ j ≤ d, X.inp (3 + 2 * ((d + 1) * r + j)) = Nm r j)
    (hinpD : ∀ j ≤ d, X.inp (4 + 2 * ((d + 1) * r + j)) = Dn r j)
    (hM1 : 1 ≤ Mh) (hNm : ∀ j ≤ d, |Nm r j| ≤ Mh) (hDn : ∀ j ≤ d, 1 ≤ Dn r j ∧ Dn r j ≤ Mh)
    (hME : Mh ≤ 2 ^ E) (hDS1 : 1 ≤ DS) (bDS : DS ≤ 2 ^ E) (bDX : |DX| ≤ 2 ^ (4 * E))
    (byv : ∀ k, |yv k| ≤ 2 ^ (7 * E + 2)) (bmu : ∀ k, |muS k| ≤ 2 ^ E)
    (bbN : |bN| ≤ 2 ^ tG d E) (bbD : |bD| ≤ 2 ^ tG d E) (hdE : d ≤ 2 ^ E) (hℓ : 3 * (E * d) + 30 * E + 5 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xR2row L) σ ((18 * d + 28) + ((d * 10 + 5) + ((d * 10 + 5) + (5 + 8)))) (fun σ' =>
      σ'.sc sBN = ((if 0 < gDI Nm Dn muS DS DX r ∧ bN * gDI Nm Dn muS DS DX r < gNI Nm Dn yv r * bD
        then gNI Nm Dn yv r else bN : ℤ) : ℝ) ∧
      σ'.sc sBD = ((if 0 < gDI Nm Dn muS DS DX r ∧ bN * gDI Nm Dn muS DS DX r < gNI Nm Dn yv r * bD
        then gDI Nm Dn muS DS DX r else bD : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA SG NGr AG σ σ') := by
  obtain ⟨hS, hN, hAr⟩ := hlay
  simp only [oE, rEE, aWE] at hS hN hAr
  have hda := asz_lt hL (a := 0) (by romega)
  have hdℓ : (d : ℤ) ≤ 2 ^ E := by exact_mod_cast hdE
  have hdm : ∀ a : ℕ, (d : ℤ) * 2 ^ a ≤ 2 ^ (E + a) := fun a => by
    rw [pow_add]; exact mul_le_mul_of_nonneg_right hdℓ (by positivity)
  have hMp : Mh ^ (d + 2) ≤ 2 ^ (E * d + 2 * E) := by
    rw [show E * d + 2 * E = E * (d + 2) by ring, pow_mul]; exact pow_le_pow_left₀ (by omega) hME _
  have bA : ∀ j ≤ d, |rowA Nm Dn d r j| ≤ 2 ^ (E * d + 2 * E) := fun j hj => (rowA_abs hM1 hNm hDn hj).trans hMp
  set av : Fin d → ℤ := fun j => rowA Nm Dn d r j with hav
  have bav : ∀ k, |av k| ≤ 2 ^ (E * d + 2 * E) := fun k => bA k k.2.le
  set gN := gNI Nm Dn yv r with hgN
  set ta := av ⬝ᵥ muS with hta
  set gD := gDI Nm Dn muS DS DX r with hgD
  have bgN : |gN| ≤ 2 ^ tG d E := by
    have := dot_abs_le bav byv hdE
    exact this.trans (pow_mono_z (by unfold tG; omega))
  have bta : |ta| ≤ 2 ^ (E * d + 4 * E) := by
    have := dot_abs_le bav bmu hdE
    exact this.trans (pow_mono_z (by omega))
  have bsB : |rowA Nm Dn d r d * DS| ≤ 2 ^ (E * d + 3 * E) := by
    rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < DS)]
    calc |rowA Nm Dn d r d| * DS ≤ 2 ^ (E * d + 2 * E) * 2 ^ E :=
          mul_le_mul (bA d le_rfl) bDS (by omega) (by positivity)
      _ = 2 ^ (E * d + 3 * E) := by ring
  have bgD : |gD| ≤ 2 ^ tG d E := by
    have h4 : |rowA Nm Dn d r d * DS - ta| ≤ 2 ^ (E * d + 4 * E + 1) := by
      refine (abs_sub _ _).trans ?_
      have := bsB.trans (pow_mono_z (show E * d + 3 * E ≤ E * d + 4 * E by omega))
      rw [pow_succ]; linarith
    rw [hgD, gDI, abs_mul]
    calc |rowA Nm Dn d r d * DS - av ⬝ᵥ muS| * |DX| ≤ 2 ^ (E * d + 4 * E + 1) * 2 ^ (4 * E) :=
          mul_le_mul h4 bDX (abs_nonneg _) (by positivity)
      _ = 2 ^ (E * d + 8 * E + 1) := by ring
      _ ≤ 2 ^ tG d E := pow_mono_z (by unfold tG; omega)
  have hℓ2 : ∀ {a : ℕ}, a < ℓ → (2 : ℤ) ^ a < 2 ^ ℓ := fun h => pow_lt_pow_right₀ (by norm_num) h
  -- step 1: row `r`
  have hkk : (d + 1) * (r + 1) ≤ (d + 1) * m := Nat.mul_le_mul_left _ hr
  refine XV.seq (XV.inRow hL (sD := sRD) (sT := sRT) (sN := sRN) (sQ := sRQ) (sB := sRB) (sDn := sDS)
    (aRow := aRw) (nI := rI) (nT := rTT) (nj := rjj) (nd := rD) (nd1 := rD1) (nk := rK) (none := rOne) (k := r)
    (Mh := Mh) (D := DS) (Nm := Nm r) (Dn := Dn r) (by qomega) (by qomega) (by qomega) (by qomega) (by qomega)
    (by qomega) (by decide) (by qomega) (by qomega) (by qomega) (by qomega) (by qomega) (by qomega) (by qomega)
    (by qomega) (by decide) hD hD1 hK h1 hDS (by omega) (by omega) (by unfold asz at hda; omega) hinpN hinpD hDS1
    hM1 hNm hDn ?_) fun σa ⟨ra, rb, da, Fa⟩ => ?_
  · calc Mh ^ (d + 2) * DS ≤ 2 ^ (E * d + 2 * E) * 2 ^ E := mul_le_mul hMp bDS (by omega) (by positivity)
      _ = 2 ^ (E * d + 3 * E) := by ring
      _ < 2 ^ ℓ := hℓ2 (by omega)
  have ra' : ∀ k : Fin d, σa.arr aRw k = av k := fun k => by rw [ra k k.2]; rfl
  have rb' : σa.sc sRB = ((rowA Nm Dn d r d * DS : ℤ) : ℝ) := by rw [rb]; rfl
  have sa : ∀ y, y ≠ sRD → y ≠ sRT → y ≠ sRN → y ≠ sRQ → y ≠ sRB → σa.sc y = σ.sc y := fun y h1 h2 h3 h4 h5 =>
    Fa.2.1 y (by tauto)
  have na : ∀ j, j ≠ rI → j ≠ rTT → j ≠ rjj → σa.nat j = σ.nat j := fun j h1 h2 h3 => Fa.1 j (by tauto)
  have aa : ∀ b k, b ≠ aRw → σa.arr b k = σ.arr b k := fun b k h => Fa.2.2.1 b k fun h' => h h'.1
  -- step 2: `g_N = â·y`
  have hZd : ∀ k, |av k| ≤ 2 ^ (E * d + 9 * E + 2) := fun k => (bav k).trans (pow_mono_z (by omega))
  have hZy : ∀ k, |yv k| ≤ 2 ^ (E * d + 9 * E + 2) := fun k => (byv k).trans (pow_mono_z (by omega))
  have hZm : ∀ k, |muS k| ≤ 2 ^ (E * d + 9 * E + 2) := fun k => (bmu k).trans (pow_mono_z (by omega))
  have hdot : d * 2 ^ (2 * (E * d + 9 * E + 2)) < 2 ^ ℓ := by
    have h := lt_of_le_of_lt (hdm (2 * (E * d + 9 * E + 2))) (hℓ2 (a := E + 2 * (E * d + 9 * E + 2)) (by omega))
    exact_mod_cast h
  refine XV.seq (XV.dot (X := X) (ℓa := ℓa) (ℓ := ℓ) (σ := σa) (E := E * d + 9 * E + 2) (x := av) (y := yv) hL
    (z := sZ) (r := sGN) (t := tR) (ax := aRw) (ay := aYv) (nr := rr) (nk := rk) (nd := rD) (none := rOne)
    (by qomega) (by qomega) (by qomega) (by qomega) (by rw [sa _ (by qomega) (by qomega) (by qomega) (by qomega)
    (by qomega), hz]) (by qomega) (by qomega) (by qomega) (by qomega) (by qomega) (by qomega) (by decide)
    (by rw [na _ (by qomega) (by qomega) (by qomega), hD]) (by rw [na _ (by qomega) (by qomega) (by qomega), h1])
    ra' (fun k => by rw [aa _ _ (by qomega), hy k]) hZd hZy (by omega) hdot) fun σb ⟨sb, db, Fb⟩ => ?_
  have sb' : ∀ y, y ≠ sGN → y < tR → σb.sc y = σa.sc y := fun y h h' => Fb.2.1 y (by omega)
  have nb : ∀ j, j ≠ rk → j ≠ rr → σb.nat j = σa.nat j := fun j h h' => Fb.1 j (by tauto)
  have ab' : ∀ b k, σb.arr b k = σa.arr b k := fun b k => Fb.2.2.1 b k id
  -- step 3: `t = â·μ̂_S`
  refine XV.seq (XV.dot (X := X) (ℓa := ℓa) (ℓ := ℓ) (σ := σb) (E := E * d + 9 * E + 2) (x := av) (y := muS) hL
    (z := sZ) (r := sTa) (t := tR) (ax := aRw) (ay := aMuS) (nr := rr) (nk := rk) (nd := rD) (none := rOne)
    (by qomega) (by qomega) (by qomega) (by qomega) (by rw [sb' _ (by qomega) (by qomega),
      sa _ (by qomega) (by qomega) (by qomega) (by qomega) (by qomega), hz]) (by qomega) (by qomega) (by qomega)
    (by qomega) (by qomega) (by qomega) (by decide)
    (by rw [nb _ (by qomega) (by qomega), na _ (by qomega) (by qomega) (by qomega), hD])
    (by rw [nb _ (by qomega) (by qomega), na _ (by qomega) (by qomega) (by qomega), h1])
    (fun k => by rw [ab', ra' k]) (fun k => by rw [ab', aa _ _ (by qomega), hmu k]) hZd hZm (by omega) hdot)
    fun σc ⟨sc, dc, Fc⟩ => ?_
  have sc' : ∀ y, y ≠ sTa → y < tR → σc.sc y = σb.sc y := fun y h h' => Fc.2.1 y (by omega)
  have nc : ∀ j, j ≠ rk → j ≠ rr → σc.nat j = σb.nat j := fun j h h' => Fc.1 j (by tauto)
  -- step 4: `g_D`
  have hzc : σc.sc sZ = 0 := by
    rw [sc' _ (by qomega) (by qomega), sb' _ (by qomega) (by qomega),
      sa _ (by qomega) (by qomega) (by qomega) (by qomega) (by qomega), hz]
  have rbc : σc.sc sRB = ((rowA Nm Dn d r d * DS : ℤ) : ℝ) := by
    rw [sc' _ (by qomega) (by qomega), sb' _ (by qomega) (by qomega), rb']
  have dxc : σc.sc sDX = (DX : ℝ) := by
    rw [sc' _ (by qomega) (by qomega), sb' _ (by qomega) (by qomega),
      sa _ (by qomega) (by qomega) (by qomega) (by qomega) (by qomega), hDX]
  have e4 : E * d + 3 * E ≤ E * d + 4 * E := by omega
  refine XV.seq (XV.ieRun (X := X) (ℓa := ℓa) (ℓ := ℓ) (σ := σc) (E := E * d + 4 * E) (v := gD) hL (z := sZ)
    (x := sGD) (t := tR) (e := ieGD) (by simp [ieGD, IE.WF]; qomega) (by qomega) (by qomega)
    (by rw [ieGD_facts.2.1]; qomega) hzc
    ⟨⟨⟨_, rbc, bsB.trans (pow_mono_z e4)⟩, ⟨ta, sc, bta⟩⟩, ⟨DX, dxc, bDX.trans (pow_mono_z (by omega))⟩⟩
    (top_lt ieGD_facts.2.2 (by omega))
    (by simp only [ieGD, IE.eval, RealRAM.Op2.eval, rbc, sc, dxc, hgD, gDI]; push_cast; ring))
    fun σd ⟨sd, _, dd, Pd⟩ => ?_
  -- step 5: the update
  have sd' : ∀ y, y ≠ sGD → y < tR → σd.sc y = σc.sc y := fun y h h' => Pd.2.1 y (by omega)
  have zd : σd.sc sZ = 0 := by rw [sd' _ (by qomega) (by qomega), hzc]
  have bNd : σd.sc sBN = (bN : ℝ) := by
    rw [sd' _ (by qomega) (by qomega), sc' _ (by qomega) (by qomega), sb' _ (by qomega) (by qomega),
      sa _ (by qomega) (by qomega) (by qomega) (by qomega) (by qomega), hbN]
  have bDd : σd.sc sBD = (bD : ℝ) := by
    rw [sd' _ (by qomega) (by qomega), sc' _ (by qomega) (by qomega), sb' _ (by qomega) (by qomega),
      sa _ (by qomega) (by qomega) (by qomega) (by qomega) (by qomega), hbD]
  have gNd : σd.sc sGN = (gN : ℝ) := by
    rw [sd' _ (by qomega) (by qomega), sc' _ (by qomega) (by qomega), sb]; rfl
  have Fd : FrameA SG NGr AG σ σd := by
    refine (((Fa.mono incS_row incN_row (fun b k h => h.1)).trans
      (Fb.mono (incS_x (by qomega)) incN_dot (fun b k h => h.elim))).trans
      (Fc.mono (incS_x (by qomega)) incN_dot (fun b k h => h.elim))).trans
      ((FrameA.ofP Pd).mono (incS_x (by qomega)) (fun j h => h.elim) (fun b k h => h))
  have ddd : σd.draws = σ.draws := by rw [dd, dc, db, da]
  have hT : 2 * tG d E < ℓ := by unfold tG; omega
  have lt1 : ∀ {x : ℤ}, |x| ≤ 2 ^ tG d E → |(x : ℝ)| < 2 ^ ℓ := fun h =>
    XV.abs_int_lt (lt_of_le_of_lt h (hℓ2 (by omega)))
  have lt2 : ∀ {x y : ℤ}, |x| ≤ 2 ^ tG d E → |y| ≤ 2 ^ tG d E → |((x * y : ℤ) : ℝ)| < 2 ^ ℓ := fun hx hy =>
    XV.abs_int_lt (by
      rw [abs_mul]
      calc |_| * |_| ≤ (2 : ℤ) ^ tG d E * 2 ^ tG d E := mul_le_mul hx hy (abs_nonneg _) (by positivity)
        _ = 2 ^ (2 * tG d E) := by ring
        _ < 2 ^ ℓ := hℓ2 hT)
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp
  refine XV.mono (K := 6 + 2) (XV.ifS_skip hL (x := sZ) (y := sGD) (by qomega) (by qomega) (by rw [zd]; exact h0)
    (by rw [sd]; exact lt1 bgD) (fun hc => ?_) (fun hc => ?_)) le_rfl fun _ h => h
  · have hgD0 : 0 < gD := by rw [zd, sd] at hc; exact_mod_cast hc
    refine XV.mono (K := 1 + (1 + (2 + 2))) ?_ (by norm_num) fun _ h => h
    refine XV.seq (XV.sop2 hL (σ := σd) (x := sC1) (a := sBN) (b := sGD) (by qomega) (by qomega) (by qomega) .mul
      (by intro h; cases h) (by rw [bNd]; exact lt1 bbN) (by rw [sd]; exact lt1 bgD)
      (by rw [bNd, sd]; simp only [RealRAM.Op2.eval]; exact_mod_cast lt2 bbN bgD)) fun σe ee => ?_
    subst ee
    refine XV.seq (XV.sop2 hL (x := sC2) (a := sGN) (b := sBD) (by qomega) (by qomega) (by qomega) .mul
      (by intro h; cases h) (by simp only [Env.setSc_sc]; rw [ite_eq_right (by qomega), gNd]; exact lt1 bgN)
      (by simp only [Env.setSc_sc]; rw [ite_eq_right (by qomega), bDd]; exact lt1 bbD)
      (by simp only [Env.setSc_sc]; rw [ite_eq_right (by qomega), ite_eq_right (by qomega), gNd, bDd];
          simp only [RealRAM.Op2.eval]; exact_mod_cast lt2 bgN bbD)) fun σf ef => ?_
    subst ef
    set σf := (σd.setSc sC1 (RealRAM.Op2.eval .mul (σd.sc sBN) (σd.sc sGD))).setSc sC2
      (RealRAM.Op2.eval .mul ((σd.setSc sC1 (RealRAM.Op2.eval .mul (σd.sc sBN) (σd.sc sGD))).sc sGN)
        ((σd.setSc sC1 (RealRAM.Op2.eval .mul (σd.sc sBN) (σd.sc sGD))).sc sBD)) with hσf
    have c1f : σf.sc sC1 = ((bN * gD : ℤ) : ℝ) := by
      rw [hσf, scO _ (by qomega), scS, bNd, sd]; simp [RealRAM.Op2.eval]
    have c2f : σf.sc sC2 = ((gN * bD : ℤ) : ℝ) := by
      rw [hσf, scS, scO _ (by qomega), scO _ (by qomega), gNd, bDd]; simp [RealRAM.Op2.eval]
    have scf : ∀ y, y ≠ sC1 → y ≠ sC2 → σf.sc y = σd.sc y := fun y h h' => by
      rw [hσf, scO _ h', scO _ h]
    have Ff : FrameA SG NGr AG σ σf := (Fd.setSc (by qomega) _).setSc (by qomega) _
    have dff : σf.draws = σ.draws := by simp only [hσf, Env.setSc_draws, ddd]
    refine XV.ifS_skip hL (x := sC1) (y := sC2) (by qomega) (by qomega) (by rw [c1f]; exact lt2 bbN bgD)
      (by rw [c2f]; exact lt2 bgN bbD) (fun hc2 => ?_) (fun hc2 => ?_)
    · have hcmp : bN * gD < gN * bD := by rw [c1f, c2f] at hc2; exact_mod_cast hc2
      have hcond : 0 < gD ∧ bN * gD < gN * bD := ⟨hgD0, hcmp⟩
      refine XV.seq (K₁ := 1) (K₂ := 1) (XV.sop2 hL (σ := σf) (x := sBN) (a := sGN) (b := sZ) (by qomega) (by qomega) (by qomega) .add
        (by intro h; cases h) (by rw [scf _ (by qomega) (by qomega), gNd]; exact lt1 bgN)
        (by rw [scf _ (by qomega) (by qomega), zd]; exact h0)
        (by rw [scf _ (by qomega) (by qomega), scf _ (by qomega) (by qomega), gNd, zd]; simp only [RealRAM.Op2.eval,
          add_zero]; exact lt1 bgN)) fun σg eg => ?_
      subst eg
      refine XV.mono (XV.sop2 hL (x := sBD) (a := sGD) (b := sZ) (by qomega) (by qomega) (by qomega) .add
        (by intro h; cases h) (by simp only [Env.setSc_sc]; rw [ite_eq_right (by qomega), scf _ (by qomega) (by qomega), sd]; exact lt1 bgD)
        (by simp only [Env.setSc_sc]; rw [ite_eq_right (by qomega), scf _ (by qomega) (by qomega), zd]; exact h0)
        (by simp only [Env.setSc_sc]; rw [ite_eq_right (by qomega), ite_eq_right (by qomega), scf _ (by qomega) (by qomega),
          scf _ (by qomega) (by qomega), sd, zd]; simp only [RealRAM.Op2.eval, add_zero]; exact lt1 bgD))
        le_rfl fun σh eh => ?_
      subst eh
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [scO _ (by qomega), scS, scf _ (by qomega) (by qomega), scf _ (by qomega) (by qomega), gNd, zd,
          ite_eq_left hcond]
        simp [RealRAM.Op2.eval]
      · rw [scS, scO _ (by qomega : sGD ≠ sBN), scO _ (by qomega : sZ ≠ sBN), scf sGD (by qomega) (by qomega),
          scf sZ (by qomega) (by qomega), sd, zd, ite_eq_left hcond]
        simp [RealRAM.Op2.eval]
      · simp only [Env.setSc_draws, dff]
      · exact (Ff.setSc (by qomega) _).setSc (by qomega) _
    · have hcmp : ¬ (bN * gD < gN * bD) := by rw [c1f, c2f] at hc2; exact_mod_cast hc2
      have hcond : ¬ (0 < gD ∧ bN * gD < gN * bD) := fun h => hcmp h.2
      refine ⟨?_, ?_, dff, Ff⟩
      · rw [scf _ (by qomega) (by qomega), bNd, ite_eq_right hcond]
      · rw [scf _ (by qomega) (by qomega), bDd, ite_eq_right hcond]
  · have hgD0 : ¬ 0 < gD := by rw [zd, sd] at hc; exact_mod_cast hc
    have hcond : ¬ (0 < gD ∧ bN * gD < gN * bD) := fun h => hgD0 h.1
    exact ⟨by rw [bNd, ite_eq_right hcond], by rw [bDd, ite_eq_right hcond], ddd, Fd⟩

/-! ## The rows -/

theorem bestG_cases (num den : ℕ → ℤ) : ∀ r, bestG num den r = (0, 1) ∨
    ∃ k < r, bestG num den r = (num k, den k)
  | 0 => Or.inl rfl
  | r + 1 => by
    rw [bestG]
    split_ifs
    · exact Or.inr ⟨r, by omega, rfl⟩
    · rcases bestG_cases num den r with h | ⟨k, hk, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, h⟩

theorem bestG_abs {num den : ℕ → ℤ} {T r : ℕ} (hT : ∀ k < r, |num k| ≤ 2 ^ T ∧ |den k| ≤ 2 ^ T) :
    |(bestG num den r).1| ≤ 2 ^ T ∧ |(bestG num den r).2| ≤ 2 ^ T := by
  rcases bestG_cases num den r with h | ⟨k, hk, h⟩
  · rw [h]; exact ⟨by simp, by simp [one_le_pow₀]⟩
  · rw [h]; exact hT k hk

set_option maxHeartbeats 4000000 in
/-- **The gauge**: the pair `bestG g_N g_D m` over the input rows. -/
theorem XV.r2g {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {E m : ℕ} {Nm Dn : ℕ → ℕ → ℤ} {Mh DS DX : ℤ} {yv muS : Fin d → ℤ}
    (hD : σ.nat rD = d) (hM : σ.nat rM = m) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hDS : σ.sc sDS = DS) (hDX : σ.sc sDX = DX) (hy : ∀ k : Fin d, σ.arr aYv k = yv k)
    (hmu : ∀ k : Fin d, σ.arr aMuS k = muS k)
    (hoff : 3 + 2 * ((d + 1) * m) ≤ X.off) (hma : 4 + 2 * ((d + 1) * m) < 2 ^ ℓa)
    (hinpN : ∀ r < m, ∀ j ≤ d, X.inp (3 + 2 * ((d + 1) * r + j)) = Nm r j)
    (hinpD : ∀ r < m, ∀ j ≤ d, X.inp (4 + 2 * ((d + 1) * r + j)) = Dn r j)
    (hM1 : 1 ≤ Mh) (hNm : ∀ r < m, ∀ j ≤ d, |Nm r j| ≤ Mh) (hDn : ∀ r < m, ∀ j ≤ d, 1 ≤ Dn r j ∧ Dn r j ≤ Mh)
    (hME : Mh ≤ 2 ^ E) (hDS1 : 1 ≤ DS) (bDS : DS ≤ 2 ^ E) (bDX : |DX| ≤ 2 ^ (4 * E))
    (byv : ∀ k, |yv k| ≤ 2 ^ (7 * E + 2)) (bmu : ∀ k, |muS k| ≤ 2 ^ E)
    (hdE : d ≤ 2 ^ E) (hℓ : 3 * (E * d) + 30 * E + 5 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xR2g L) σ (r2gUnits d m) (fun σ' =>
      σ'.sc sBN = ((bestG (gNI Nm Dn yv) (gDI Nm Dn muS DS DX) m).1 : ℝ) ∧
      σ'.sc sBD = ((bestG (gNI Nm Dn yv) (gDI Nm Dn muS DS DX) m).2 : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA SG NG AG σ σ' ∧
      |(bestG (gNI Nm Dn yv) (gDI Nm Dn muS DS DX) m).1| ≤ 2 ^ tG d E ∧
      |(bestG (gNI Nm Dn yv) (gDI Nm Dn muS DS DX) m).2| ≤ 2 ^ tG d E) := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  have hℓ2 : ∀ {a : ℕ}, a < ℓ → (2 : ℤ) ^ a < 2 ^ ℓ := fun h => pow_lt_pow_right₀ (by norm_num) h
  have hda := asz_lt hL (a := 0) (by omega)
  -- the bounds of the rows
  have bT : ∀ k < m, |gNI Nm Dn yv k| ≤ 2 ^ tG d E ∧ |gDI Nm Dn muS DS DX k| ≤ 2 ^ tG d E := by
    intro k hk
    have hMp : Mh ^ (d + 2) ≤ 2 ^ (E * d + 2 * E) := by
      rw [show E * d + 2 * E = E * (d + 2) by ring, pow_mul]; exact pow_le_pow_left₀ (by omega) hME _
    have bav : ∀ j : Fin d, |rowA Nm Dn d k j| ≤ 2 ^ (E * d + 2 * E) := fun j =>
      (rowA_abs hM1 (hNm k hk) (hDn k hk) j.2.le).trans hMp
    refine ⟨(dot_abs_le bav byv hdE).trans (pow_mono_z (by unfold tG; omega)), ?_⟩
    have bsB : |rowA Nm Dn d k d * DS| ≤ 2 ^ (E * d + 3 * E) := by
      rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < DS)]
      calc |rowA Nm Dn d k d| * DS ≤ 2 ^ (E * d + 2 * E) * 2 ^ E :=
            mul_le_mul ((rowA_abs hM1 (hNm k hk) (hDn k hk) le_rfl).trans hMp) bDS (by omega) (by positivity)
        _ = 2 ^ (E * d + 3 * E) := by ring
    have bta := (dot_abs_le bav bmu hdE).trans (pow_mono_z (show E * d + 2 * E + E + E ≤ E * d + 4 * E by omega))
    have h4 : |rowA Nm Dn d k d * DS - (fun j : Fin d => rowA Nm Dn d k j) ⬝ᵥ muS| ≤ 2 ^ (E * d + 4 * E + 1) := by
      refine (abs_sub _ _).trans ?_
      have := bsB.trans (pow_mono_z (show E * d + 3 * E ≤ E * d + 4 * E by omega))
      rw [pow_succ]; linarith
    rw [gDI, abs_mul]
    calc _ ≤ (2 : ℤ) ^ (E * d + 4 * E + 1) * 2 ^ (4 * E) := mul_le_mul h4 bDX (abs_nonneg _) (by positivity)
      _ = 2 ^ (E * d + 8 * E + 1) := by ring
      _ ≤ 2 ^ tG d E := pow_mono_z (by unfold tG; omega)
  have hmA : m < 2 ^ ℓa := by
    have : m ≤ 4 + 2 * ((d + 1) * m) := by nlinarith
    omega
  -- `b_N := 0`, `b_D := 1`, `rD1 := d + 1`
  refine XV.mono (K := 1 + (1 + (1 + (m * ((18 * d + 28) + ((d * 10 + 5) + ((d * 10 + 5) + (5 + 8))) + 3) + 3))))
    ?_ le_rfl fun _ h => h
  refine XV.seq (XV.sop2 hL (σ := σ) (x := sBN) (a := sZ) (b := sZ) (by qomega) (by qomega) (by qomega) .add
    (by intro h; cases h) (by rw [hz]; simp) (by rw [hz]; simp) (by rw [hz]; simp [RealRAM.Op2.eval])) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.sconst hL (x := sBD) (by qomega) 1 rfl (by rw [Rat.cast_one, abs_one]; exact_mod_cast Nat.one_lt_two_pow (by omega : ℓ ≠ 0))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nadd hL (i := rD1) (a := rD) (b := rOne) (by qomega) (by qomega) (by qomega)
    (by simp only [Env.setSc_nat, Env.setSc_nat, hD]; unfold asz at hda; nlinarith)
    (by simp only [Env.setSc_nat, h1]; omega)) fun σ3 e3 => ?_
  subst e3
  set σ0 := (((σ.setSc sBN (RealRAM.Op2.eval .add (σ.sc sZ) (σ.sc sZ))).setSc sBD ((1 : ℚ) : ℝ)).setNat rD1
    (((σ.setSc sBN (RealRAM.Op2.eval .add (σ.sc sZ) (σ.sc sZ))).setSc sBD ((1 : ℚ) : ℝ)).nat rD +
      ((σ.setSc sBN (RealRAM.Op2.eval .add (σ.sc sZ) (σ.sc sZ))).setSc sBD ((1 : ℚ) : ℝ)).nat rOne)) with hσ0
  have F0 : FrameA SG NG AG σ σ0 :=
    (((FrameA.refl _ _ _ σ).setSc (by qomega) _).setSc (by qomega) _).setNat (by qomega) _
  let J : ℕ → Env d → Prop := fun r σ' =>
    σ'.sc sBN = ((bestG (gNI Nm Dn yv) (gDI Nm Dn muS DS DX) r).1 : ℝ) ∧
    σ'.sc sBD = ((bestG (gNI Nm Dn yv) (gDI Nm Dn muS DS DX) r).2 : ℝ) ∧
    σ'.nat rD1 = d + 1 ∧ σ'.draws = σ.draws ∧ FrameA SG NG AG σ σ'
  refine XV.mono (XV.forN hL (i := rK) (n := rM) (one := rOne) (body := xR2row L) (by qomega) (by qomega)
    (by qomega) (by qomega) (by qomega) m _ hmA J σ0
    (by simp [hσ0, hM]) (by simp [hσ0, h1])
    ⟨by simp [hσ0, bestG, hz, RealRAM.Op2.eval], by simp [hσ0, bestG], by simp [hσ0, hD, h1],
      by simp [hσ0], F0.setNat (by qomega) 0⟩ ?_) le_rfl fun σ' ⟨⟨h1', h2', _, h4', h5'⟩, _⟩ =>
      ⟨h1', h2', h4', h5', (bestG_abs (fun k hk => bT k hk)).1, (bestG_abs (fun k hk => bT k hk)).2⟩
  intro r hr σ' ⟨hb1, hb2, hd1, hdr, F'⟩ hrk hrm hr1
  have bb := bestG_abs (r := r) (fun k hk => bT k (by omega))
  have nn : ∀ j, ¬ NG j → σ'.nat j = σ.nat j := F'.1
  have ss : ∀ y, ¬ SG y → σ'.sc y = σ.sc y := F'.2.1
  have aa : ∀ b k, b ≠ aRw → σ'.arr b k = σ.arr b k := fun b k h => F'.2.2.1 b k h
  refine XV.mono (XV.r2row hL hlay (σ := σ') (E := E) (m := m) (r := r) (Nm := Nm) (Dn := Dn) (Mh := Mh) (DS := DS)
    (DX := DX) (yv := yv) (muS := muS) hr (by rw [nn _ (by qomega), hD]) hd1 hrk hr1
    (by rw [ss _ (by qomega), hz]) (by rw [ss _ (by qomega), hDS]) (by rw [ss _ (by qomega), hDX])
    (fun k => by rw [aa _ _ (by qomega), hy k]) (fun k => by rw [aa _ _ (by qomega), hmu k]) hb1 hb2 hoff hma
    (hinpN r hr) (hinpD r hr) hM1 (hNm r hr) (hDn r hr) hME hDS1 bDS bDX byv bmu bb.1 bb.2 hdE hℓ) le_rfl
    fun σ'' ⟨s1, s2, s3, F''⟩ => ?_
  have F3 := F'.trans (F''.mono (fun y h => h) incN_g (fun _ _ h => h))
  refine ⟨by rw [F''.1 rK (by qomega), hrk], by rw [F''.1 rM (by qomega), hrm], by rw [F''.1 rOne (by qomega), hr1],
    ?_, ?_, ?_, ?_, F3.setNat (by qomega) _⟩
  · rw [Env.setNat_sc, s1, bestG]
    split_ifs <;> rfl
  · rw [Env.setNat_sc, s2, bestG]
    split_ifs <;> rfl
  · rw [Env.setNat_nat, ite_eq_right (by qomega), F''.1 rD1 (by qomega), hd1]
  · rw [Env.setNat_draws, s3, hdr]

end AdversarialBco.Bit.Transfer.BLM
