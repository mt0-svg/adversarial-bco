/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOR2q

@[expose] public section

/-!
# BL-O's R2 in mode `run`

`xR2 L`: v2.1's point `X'` (`xR2x`: `Â Γ` in `aWv`, `D_X`, `X̂`, `Â_S X̂`), the CM constants (`xcmc`), `jG`, the
gauge's point, centre and radius (ProgOR2a.lean); the gauge `xgaugeU` with the CM test at the position map `xtst`;
then `b_N = H_n u`, `b_D = D_X 2^jG` and v2.1's scale and play buffer (`xR2p`).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-! ## The code -/

/-- The gauge's cells: the point `aXD`, the centre `aA0`, `H_n'` in `300`, `D_X` in `301`, `jG` in `rJG`, `2^jG` in
`302`, the test point `aTP`, the answer `rGt`, the counter in `303`, scratch slots from `304`, registers from `42`. -/
def gLay : GaugeLay := ⟨aXD, aA0, 300, 301, rJG, 302, aTP, rGt, 303, 304, 42⟩

/-- The test's cells: slots from `400`, registers and arrays from `48`. -/
def qLay : TstLay := ⟨400, 48, 48⟩

/-- R2 before the gauge. -/
def xR2pre (L : Layout) : XCmd :=
  .seq (xR2x L) (.seq (xcmc L qLay) (.seq (xjG L) (.seq (xpts L) (xhn L))))

/-- R2 after the gauge: `b_N := H_n u`, `b_D := D_X 2^jG`, the scale and the play buffer. -/
def xR2post (L : Layout) : XCmd :=
  .seq (toX (VL.sop2 L .mul sBN sHn 303)) (.seq (toX (VL.sop2 L .mul sBD sDX 302)) (xR2p L))

/-- **R2 in mode `run`.** -/
def xR2 (L : Layout) : XCmdO :=
  .seq (.base (xR2pre L)) (.seq (xgaugeU L gLay (xtst L qLay aTP rGt)) (.base (xR2post L)))

/-- The cells R2 changes before the gauge. -/
def SPre (y : ℕ) : Prop := (sZeta < y ∧ y < 64) ∨ tR ≤ y
def NPre (j : ℕ) : Prop := rD2 < j ∧ j < 64
def APre (a _k : ℕ) : Prop := aGam < a ∧ a < 34

/-- `r2omega` with the layouts and the frames of R2 unfolded. -/
macro "p2omega" : tactic => `(tactic| ((try simp only [qLay, gLay, SPre, NPre, APre, SR2, NR2, AR2, tR, sZeta, rD2,
  aGam, ne_eq, not_or, not_and, not_not] at *) <;> r2omega))

theorem sum_abs_le {x : Fin d → ℤ} {B : ℕ} (bx : ∀ k, |x k| ≤ 2 ^ B) (hdB : d ≤ 2 ^ B) :
    |(∑ k, |x k|)| ≤ 2 ^ (2 * B) := by
  rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  calc ∑ k, |x k| ≤ ∑ _k : Fin d, (2 : ℤ) ^ B := Finset.sum_le_sum fun k _ => bx k
    _ = d * 2 ^ B := by simp
    _ ≤ 2 ^ B * 2 ^ B := mul_le_mul_of_nonneg_right (by exact_mod_cast hdB) (by positivity)
    _ = 2 ^ (2 * B) := by rw [two_mul, pow_add]

theorem jGv_le {p Ri E : ℕ} (hdE : d ≤ E) (hEpow : E < 2 ^ E) (bRi : Ri ≤ 2 ^ E) (hpE : p ≤ E) :
    jGv p d Ri ≤ 3 * E + 5 := by
  have h2 : 2 * d * Ri ≤ 2 ^ (2 * E + 1) :=
    calc 2 * d * Ri ≤ 2 * 2 ^ E * 2 ^ E := Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hdE.trans hEpow.le)) bRi
      _ = 2 ^ (2 * E + 1) := by ring
  have := Nat.clog_le_of_le_pow h2
  unfold jGv; omega

/-! ## Before the gauge -/

set_option maxHeartbeats 8000000 in
/-- **R2 before the gauge**: `X'` (v2.1), the CM constants, `jG`, the gauge's point, centre and radius; every
persistent input below `2^E` (`Γ` below `2^{2E}`), `d ≤ E`. -/
theorem XV.r2pre {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) (hNS : 456 ≤ L.NS)
    (hNN : 64 ≤ L.NN) (hNA : 52 ≤ L.NA) {σ : Env d} {E : ℕ}
    {Ah ASh : Matrix (Fin d) (Fin d) ℤ} {Γ mh : Fin d → ℤ} {Dm PF P G lh Rn rn rd Rn0 Rd0 : ℤ} {p Ri : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hp : σ.nat rP = p)
    (hA : ∀ i k : Fin d, σ.arr aA (d * i + k) = Ah i k) (hAS : ∀ i k : Fin d, σ.arr aAS (d * i + k) = ASh i k)
    (hG : ∀ k : Fin d, σ.arr aGam k = Γ k) (hmu : ∀ k : Fin d, σ.arr aMu k = mh k)
    (hDm : σ.sc sDmu = Dm) (hPF : σ.sc s2pF = PF) (hP : σ.sc s2p = P) (hGs : σ.sc s2g = G)
    (hlh : σ.sc sLamb = lh) (hR : σ.sc sR = Rn) (hRi : σ.sc sRint = (Ri : ℝ))
    (i4 : X.inp 4 = rn) (i5 : X.inp 5 = rd) (i6 : X.inp 6 = Rn0) (i7 : X.inp 7 = Rd0) (hoff : 8 ≤ X.off)
    (hPF0 : 0 < PF) (hrn : 0 < rn) (hrd : 0 < rd) (hR0n : 0 < Rn0) (hR0d : 0 < Rd0) (hRn : 0 ≤ Rn)
    (bA : ∀ i k, |Ah i k| ≤ 2 ^ E) (bAS : ∀ i k, |ASh i k| ≤ 2 ^ E) (bG : ∀ k, |Γ k| ≤ 2 ^ (2 * E))
    (bmu : ∀ k, |mh k| ≤ 2 ^ E) (bDm : |Dm| ≤ 2 ^ E) (bPF : |PF| ≤ 2 ^ E) (bP : |P| ≤ 2 ^ E)
    (bGs : |G| ≤ 2 ^ E) (blh : |lh| ≤ 2 ^ E) (bRn : Rn ≤ 2 ^ E) (brn : rn ≤ 2 ^ E) (brd : rd ≤ 2 ^ E)
    (bR0n : Rn0 ≤ 2 ^ E) (bR0d : Rd0 ≤ 2 ^ E) (bRi : Ri ≤ 2 ^ E) (hpE : p ≤ E) (hdE : d ≤ E) (hd1 : 1 ≤ d)
    (hℓ : 50 * E + 60 ≤ ℓ) (hℓa : 50 * E + 60 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR2pre L) σ (r2xUnits d + (200 * (E + 1) + ((20 * E + 40) + ((13 * d + 10) + 5)))) (fun σ' =>
      (∀ i : Fin d, σ'.arr aWv i = (Ah *ᵥ Γ) i) ∧ σ'.sc sDX = ((Dm * PF * P * G : ℤ) : ℝ) ∧
      (∀ i : Fin d, σ'.arr aYv i = (ASh *ᵥ xhI mh Ah Γ Dm PF P G lh) i) ∧
      σ'.sc qLay.s = rn ∧ σ'.sc (qLay.s + 1) = rd ∧
      σ'.nat qLay.n = cmcK p (6 * Rn * Rn0 * rd * rd) (PF * Rd0 * rn * rn) ∧
      σ'.sc (qLay.s + 2) = 2 ^ cmcK p (6 * Rn * Rn0 * rd * rd) (PF * Rd0 * rn * rn) ∧
      σ'.nat rJG = jGv p d Ri ∧ σ'.sc 302 = 2 ^ jGv p d Ri ∧
      σ'.arr aXD 0 = ((Dm * PF * P * G : ℤ) : ℝ) ∧
      (∀ k : Fin d, σ'.arr aXD (1 + k) = xhI mh Ah Γ Dm PF P G lh k) ∧ σ'.arr aA0 0 = 1 ∧
      (∀ k : Fin d, σ'.arr aA0 (1 + k) = 0) ∧
      σ'.sc sHn = ((2 * ∑ k, |xhI mh Ah Γ Dm PF P G lh k| : ℤ) : ℝ) ∧
      σ'.sc 300 = ((hnG (2 * ∑ k, |xhI mh Ah Γ Dm PF P G lh k|) : ℤ) : ℝ) ∧
      σ'.sc 301 = ((Dm * PF * P * G : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA SPre NPre APre σ σ') := by
  have hQ : qLay.OK L := ⟨⟨by simp [qLay], by simp only [qLay]; omega⟩, ⟨by simp [qLay], by simp only [qLay]; omega⟩,
    ⟨by simp [qLay], by simp only [qLay]; omega⟩⟩
  have p2 : ∀ {a b : ℕ}, a ≤ b → (2 : ℤ) ^ a ≤ 2 ^ b := fun h => pow_le_pow_right₀ (by norm_num) h
  have up : ∀ {z : ℤ}, |z| ≤ 2 ^ E → |z| ≤ 2 ^ (2 * E) := fun h => h.trans (p2 (by omega))
  have hEpow : E < 2 ^ E := Nat.lt_two_pow_self
  have hdE2 : d ≤ 2 ^ (2 * E) := (hdE.trans hEpow.le).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- R2, the point
  refine XV.seq (XV.r2x hL hlay (σ := σ) (E := 2 * E) (Ah := Ah) (ASh := ASh) (Γ := Γ) (mh := mh) (Dm := Dm)
    (PF := PF) (P := P) (G := G) (lh := lh) hD h1 hz hA hAS hG hmu hDm hPF hP hGs hlh (fun i k => up (bA i k))
    (fun i k => up (bAS i k)) bG (fun k => up (bmu k)) (up bDm) (up bPF) (up bP) (up bGs) (up blh) hdE2
    (by omega)) fun σ1 ⟨w1, x1, xh1, y1, d1, F1⟩ => ?_
  set xh := xhI mh Ah Γ Dm PF P G lh with hxh
  set DX := Dm * PF * P * G with hDX
  have n1 : ∀ j, ¬ NR2 j → σ1.nat j = σ.nat j := F1.1
  have s1 : ∀ y, ¬ SR2 y → σ1.sc y = σ.sc y := F1.2.1
  -- the CM constants
  refine XV.seq (XV.cmc hL hQ (σ := σ1) (m := E) i4 i5 i6 i7 hoff hrn hrd hR0n hR0d hRn hPF0
    (by rw [s1 _ (by romega), hz]) (by rw [n1 _ (by romega), h1]) (by rw [n1 _ (by romega), hp])
    (by rw [s1 _ (by romega), hR]) (by rw [s1 _ (by romega), hPF]) brn brd bR0n bR0d bRn (le_of_abs_le bPF) hpE
    (by omega) (by omega)) fun σ2 ⟨c0, c1, c2, c3, d2, F2⟩ => ?_
  have n2 : ∀ j, ¬ (j = qLay.n ∨ (qLay.n + 12 ≤ j ∧ j < qLay.n + 16)) → σ2.nat j = σ1.nat j := F2.1
  have s2 : ∀ y, ¬ qLay.s ≤ y → σ2.sc y = σ1.sc y := F2.2.1
  have a2 : ∀ b k, σ2.arr b k = σ1.arr b k := fun b k => F2.2.2.1 b k id
  -- `jG`
  have hjG : jGv p d Ri ≤ 3 * E + 5 := jGv_le hdE hEpow bRi hpE
  refine XV.seq (XV.mono (XV.jG hL (σ := σ2) (p := p) (Ri := Ri) (B := E) (by omega) (by r2omega) (by omega)
    (by rw [n2 _ (by p2omega), n1 _ (by romega), hD]) (by rw [n2 _ (by p2omega), n1 _ (by romega), h1])
    (by rw [n2 _ (by p2omega), n1 _ (by romega), hp]) (by rw [s2 _ (by p2omega), s1 _ (by romega), hRi]) bRi
    (hdE.trans hEpow.le) hpE (by omega) (by omega)) (by omega) (fun _ h => h)) fun σ3 ⟨j3, q3, d3, F3⟩ => ?_
  have n3 : ∀ j, ¬ (j = rcl ∨ j = rc4 ∨ j = rJG) → σ3.nat j = σ2.nat j := F3.1
  have s3 : ∀ y, ¬ (y = s2dR ∨ y = sW2 ∨ y = 302) → σ3.sc y = σ2.sc y := F3.2.1
  have a3 : ∀ b k, σ3.arr b k = σ2.arr b k := fun b k => F3.2.2.1 b k id
  -- the point and the centre
  have bDX : |DX| ≤ 2 ^ (4 * E) := by
    rw [hDX, show 4 * E = E + E + E + E by ring]
    exact abs_mul_pow (abs_mul_pow (abs_mul_pow bDm bPF) bP) bGs
  have bxh : ∀ k, |xh k| ≤ 2 ^ (5 * (2 * E) + 2) := fun k =>
    xhI_abs (fun i k => up (bA i k)) bG (fun k => up (bmu k)) (up bDm) (up bPF) (up bP) (up bGs) (up blh) hdE2 k
  have hdB : d ≤ 2 ^ (10 * E + 2) := (hdE.trans hEpow.le).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine XV.seq (XV.mono (XV.pts hL (σ := σ3) (DX := DX) (xh := xh) (B := 10 * E + 2) (by r2omega) (by r2omega) (by r2omega)
    hd1 (by rw [n3 _ (by r2omega), n2 _ (by p2omega), n1 _ (by romega), hD])
    (by rw [n3 _ (by r2omega), n2 _ (by p2omega), n1 _ (by romega), h1])
    (by rw [s3 _ (by r2omega), s2 _ (by p2omega), s1 _ (by romega), hz])
    (by rw [s3 _ (by r2omega), s2 _ (by p2omega), x1])
    (fun k => by rw [a3, a2, xh1]) (bDX.trans (p2 (by omega))) (fun k => (bxh k).trans (p2 (by omega))) hdB
    (by omega)) (by omega) (fun _ h => h)) fun σ4 ⟨v0, vX, vA0, vA, vS, d4, F4⟩ => ?_
  have n4 : ∀ j, ¬ (j = rk2 ∨ j = rk3) → σ4.nat j = σ3.nat j := F4.1
  have s4 : ∀ y, ¬ (y = sHa ∨ y = sT2) → σ4.sc y = σ3.sc y := F4.2.1
  have a4 : ∀ b k, ¬ (b = aXD ∨ b = aA0) → σ4.arr b k = σ3.arr b k := fun b k h => F4.2.2.1 b k h
  -- the radius
  refine XV.mono (XV.hn hL (σ := σ4) (Ha := ∑ k, |xh k|) (DX := DX) (B := 20 * E + 4) (by r2omega)
    (by rw [s4 _ (by r2omega), s3 _ (by r2omega), s2 _ (by p2omega), s1 _ (by romega), hz]) vS
    (by rw [s4 _ (by r2omega), s3 _ (by r2omega), s2 _ (by p2omega), x1])
    ((sum_abs_le (fun k => (bxh k).trans (p2 (by omega))) hdB).trans (p2 (by omega)))
    (bDX.trans (p2 (by omega))) (by omega)) le_rfl fun σ5 ⟨h5n, h5g, h5d, d5, F5⟩ => ?_
  have n5 : ∀ j, σ5.nat j = σ4.nat j := fun j => F5.1 j id
  have s5 : ∀ y, ¬ (y = sHn ∨ y = 300 ∨ y = 301) → σ5.sc y = σ4.sc y := F5.2.1
  have a5 : ∀ b k, σ5.arr b k = σ4.arr b k := fun b k => F5.2.2.1 b k id
  refine ⟨fun i => ?_, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k => ?_, ?_, fun k => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a5, a4 _ _ (by r2omega), a3, a2]; exact w1 i
  · rw [s5 _ (by r2omega), s4 _ (by r2omega), s3 _ (by r2omega), s2 _ (by p2omega)]; exact x1
  · rw [a5, a4 _ _ (by r2omega), a3, a2]; exact y1 i
  · rw [s5 _ (by p2omega), s4 _ (by p2omega), s3 _ (by p2omega)]; exact c0
  · rw [s5 _ (by p2omega), s4 _ (by p2omega), s3 _ (by p2omega)]; exact c1
  · rw [n5, n4 _ (by p2omega), n3 _ (by p2omega)]; exact c2
  · rw [s5 _ (by p2omega), s4 _ (by p2omega), s3 _ (by p2omega)]; exact c3
  · rw [n5, n4 _ (by r2omega)]; exact j3
  · rw [s5 _ (by r2omega), s4 _ (by r2omega)]; exact q3
  · rw [a5]; exact v0
  · rw [a5]; exact vX k
  · rw [a5]; exact vA0
  · rw [a5]; exact vA k
  · exact h5n
  · exact h5g
  · exact h5d
  · rw [d5, d4, d3, d2, d1]
  · refine (F1.mono (fun y h => by simp only [SR2] at h; simp only [SPre]; omega)
      (fun j h => by simp only [NR2] at h; simp only [NPre]; omega)
      (fun b k h => by simp only [AR2] at h; simp only [APre]; omega)).trans ?_
    refine (F2.mono (fun y h => by simp only [qLay] at h; simp only [SPre, tR]; omega)
      (fun j h => by simp only [qLay] at h; simp only [NPre, rD2]; omega) (fun _ _ h => h.elim)).trans ?_
    refine (F3.mono (fun y h => by simp only [s2dR, sW2] at h; simp only [SPre, tR]; omega)
      (fun j h => by simp only [rcl, rc4, rJG] at h; simp only [NPre, rD2]; omega) (fun _ _ h => h.elim)).trans ?_
    refine (F4.mono (fun y h => by simp only [sHa, sT2] at h; simp only [SPre, tR]; omega)
      (fun j h => by simp only [rk2, rk3] at h; simp only [NPre, rD2]; omega)
      (fun b k h => by simp only [aXD, aA0] at h; simp only [APre, aGam]; omega)).trans ?_
    exact F5.mono (fun y h => by simp only [sHn] at h; simp only [SPre, tR]; omega) (fun _ h => h.elim)
      (fun _ _ h => h.elim)


/-! ## After the gauge -/

set_option maxHeartbeats 4000000 in
/-- **R2 after the gauge**: `b_N = H_n u`, `b_D = D_X 2^jG`, then v2.1's scale and play buffer. -/
theorem XV.r2post {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {Ep : ℕ} {Hn u DX P2 F eh DS : ℤ} {yv muS : Fin d → ℤ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hHn : σ.sc sHn = Hn) (hu : σ.sc 303 = u)
    (hDX : σ.sc sDX = DX) (h2j : σ.sc 302 = P2) (hF : σ.sc s2pF = F) (he : σ.sc sEps = eh)
    (hDS : σ.sc sDS = DS) (hy : ∀ k : Fin d, σ.arr aYv k = yv k) (hmu : ∀ k : Fin d, σ.arr aMuS k = muS k)
    (bHn : |Hn| ≤ 2 ^ tG d Ep) (bu : |u| ≤ 2 ^ tG d Ep) (bP2 : |P2| ≤ 2 ^ tG d Ep)
    (bN : |Hn * u| ≤ 2 ^ tG d Ep) (bDP : |DX * P2| ≤ 2 ^ tG d Ep)
    (bF : |F| ≤ 2 ^ Ep) (beh : |eh| ≤ 2 ^ Ep) (bDS : |DS| ≤ 2 ^ Ep) (bDX : |DX| ≤ 2 ^ (4 * Ep))
    (byv : ∀ k, |yv k| ≤ 2 ^ (7 * Ep + 2)) (bmu : ∀ k, |muS k| ≤ 2 ^ Ep) (hd1 : 1 ≤ d)
    (hℓ : 3 * (Ep * d) + 33 * Ep + 11 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xR2post L) σ (1 + (1 + r2pUnits d)) (fun σ' =>
      σ'.sc sPtN = ((ptPair (Hn * u) (DX * P2) F eh).1 : ℝ) ∧
      σ'.sc sPtD = ((ptPair (Hn * u) (DX * P2) F eh).2 : ℝ) ∧
      σ'.arr aPl 0 = ((DS * DX * (ptPair (Hn * u) (DX * P2) F eh).1 : ℤ) : ℝ) ∧
      (∀ k : Fin d, σ'.arr aPl (1 + k) =
        ((muS k * DX * (ptPair (Hn * u) (DX * P2) F eh).1 + yv k * (ptPair (Hn * u) (DX * P2) F eh).2 : ℤ) : ℝ)) ∧
      σ'.draws = σ.draws ∧ FrameA (fun y => y = sBN ∨ y = sBD ∨ SP y) NP AP σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  have hTℓ : tG d Ep < ℓ := by unfold tG; nlinarith
  have hb : ∀ z : ℤ, |z| ≤ 2 ^ tG d Ep → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) hTℓ)
  have bDX' : |DX| ≤ 2 ^ tG d Ep := bDX.trans (pow_le_pow_right₀ (by norm_num) (by unfold tG; nlinarith))
  refine XV.seq (XV.mulI hL (x := sBN) (a := sHn) (b := 303) (u := Hn) (v := u) (by p2omega) (by p2omega)
    (by p2omega) hHn hu (hb _ bHn) (hb _ bu) (hb _ bN)) fun σ1 e1 => ?_
  have s1 : ∀ y, y ≠ sBN → σ1.sc y = σ.sc y := fun y hy => by rw [e1, Env.setSc_sc, ite_eq_right hy]
  refine XV.seq (XV.mulI hL (σ := σ1) (x := sBD) (a := sDX) (b := 302) (u := DX) (v := P2) (by p2omega) (by p2omega)
    (by p2omega) (by rw [s1 _ (by p2omega), hDX]) (by rw [s1 _ (by p2omega), h2j]) (hb _ bDX') (hb _ bP2)
    (hb _ bDP)) fun σ2 e2 => ?_
  have s2 : ∀ y, y ≠ sBN → y ≠ sBD → σ2.sc y = σ.sc y := fun y hy hy' => by
    rw [e2, Env.setSc_sc, ite_eq_right hy', s1 _ hy]
  have nn : σ2.nat = σ.nat := by rw [e2, e1]; rfl
  have aa : σ2.arr = σ.arr := by rw [e2, e1]; rfl
  refine XV.mono (XV.r2p hL hlay (σ := σ2) (E := Ep) (bN := Hn * u) (bD := DX * P2) (F := F) (eh := eh) (DS := DS)
    (DX := DX) (yv := yv) (muS := muS) (by rw [nn, hD]) (by rw [nn, h1]) (by rw [s2 _ (by p2omega) (by p2omega), hz])
    (by rw [e2, Env.setSc_sc, ite_eq_right (by p2omega), e1, Env.setSc_sc, ite_eq_left rfl])
    (by rw [e2, Env.setSc_sc, ite_eq_left rfl]) (by rw [s2 _ (by p2omega) (by p2omega), hF])
    (by rw [s2 _ (by p2omega) (by p2omega), he]) (by rw [s2 _ (by p2omega) (by p2omega), hDS])
    (by rw [s2 _ (by p2omega) (by p2omega), hDX]) (fun k => by rw [aa, hy]) (fun k => by rw [aa, hmu]) bN bDP bF beh
    bDS bDX byv bmu hd1 hℓ) le_rfl fun σ3 ⟨q1, q2, q3, q4, d3, F3⟩ => ?_
  refine ⟨q1, q2, q3, q4, by rw [d3, e2, e1]; rfl, ?_⟩
  have F2 : FrameA (fun y => y = sBN ∨ y = sBD ∨ SP y) NP AP σ σ2 := by
    rw [e2, e1]; exact ((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setSc (Or.inr (Or.inl rfl)) _
  exact F2.trans (F3.mono (fun y h => Or.inr (Or.inr h)) (fun _ h => h) (fun _ _ h => h))

/-- `TstDat` is kept by every frame avoiding the cells it reads. -/
theorem tstDat_stable {Q : TstLay} {DS : ℤ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ} {Da : ℤ}
    {Na : Fin d → ℤ} {rn rd : ℤ} {k : ℕ} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop}
    (hS : ∀ y, S y → y ≠ sZ ∧ y ≠ sDS ∧ y ≠ Q.s ∧ y ≠ Q.s + 1 ∧ y ≠ Q.s + 2)
    (hN : ∀ j, N j → j ≠ rD ∧ j ≠ rOne ∧ j ≠ Q.n) (hA : ∀ b k, Ar b k → b ≠ aMuS ∧ b ≠ aAS ∧ b ≠ aC) :
    Stable (TstDat Q DS muS aS Da Na rn rd k) S N Ar := by
  intro σ σ' h F _
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := h.hcm
  exact ⟨by rw [F.1 _ fun h' => (hN _ h').1 rfl, h.hd], by rw [F.1 _ fun h' => (hN _ h').2.1 rfl, h.h1],
    by rw [F.2.1 _ fun h' => (hS _ h').1 rfl, h.hz], by rw [F.2.1 _ fun h' => (hS _ h').2.1 rfl, h.hds],
    fun i => by rw [F.2.2.1 _ _ fun h' => (hA _ _ h').1 rfl, h.hmu i],
    fun i j => by rw [F.2.2.1 _ _ fun h' => (hA _ _ h').2.1 rfl, h.has i j],
    ⟨(F.2.2.1 _ _ fun h' => (hA _ _ h').2.2 rfl).trans c0,
      fun i => (F.2.2.1 _ _ fun h' => (hA _ _ h').2.2 rfl).trans (c1 i),
      (F.2.1 _ fun h' => (hS _ h').2.2.1 rfl).trans c2, (F.2.1 _ fun h' => (hS _ h').2.2.2.1 rfl).trans c3,
      (F.1 _ fun h' => (hN _ h').2.2 rfl).trans c4, (F.2.1 _ fun h' => (hS _ h').2.2.2.2 rfl).trans c5⟩⟩

end AdversarialBco.Unified.ProgO
