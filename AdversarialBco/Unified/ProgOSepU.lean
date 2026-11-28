/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.SepGauge

@[expose] public section

/-!
# The CM and gauge blocks, uniform in `d`

`xcm d L c` and `xgauge d L g` of `SepCM` and `SepGauge` write the constant `d` into their loop bounds, so their text
depends on `d`. The blocks `xcmU L c` and `xgaugeU L g` here read `d` from the natural register `0` instead (the
register `rD` of the machine, which holds `d` throughout): one program text for every `d`. Their contracts `CMBlockOKU`
and `GaugeBlockOKU` are the contracts of `xcm` and `xgauge` with `σ.nat 0 = d` in the data, the layouts' written
naturals away from `0`, and the gauge's test block keeping the register `0` out of its frame. The proofs are those of
the contracts of `xcm` and `xgauge`, with one more unit in each preamble.
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer

variable {d : ℕ}

/-! ## The contracts -/

/-- The layout of the CM block fits `L` and the naturals it writes avoid the register `0`. -/
def CMLay.OKU (L : Layout) (c : CMLay) : Prop := CMLay.OK L c ∧ 0 < c.nt ∧ 0 < c.n0

/-- The data of the CM block, with `d` in the register `0`. -/
def CMDatU (c : CMLay) (Da : ℤ) (Na : Fin d → ℤ) (rn rd : ℤ) (k : ℕ) (σ : Env d) : Prop :=
  CMDat c Da Na rn rd k σ ∧ σ.nat 0 = d

/-- The contract of a CM block uniform in `d`, with the data `CMDatU` and the layout `CMLay.OKU`. -/
def CMBlockOKU (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (c : CMLay) (cmc : XCmdO) : Prop :=
  ∀ (Da : ℤ) (Na : Fin d → ℤ) (rn rd : ℤ) (k b bt : ℕ),
    LayOK L d ℓa → CMLay.OKU L c → 1 ≤ d → 0 < Da → 0 < rn → 0 < rd → Da < 2 ^ b → (∀ i, |Na i| < 2 ^ b) →
    rn < 2 ^ b → rd < 2 ^ b → 2 * b + bt + k + 6 ≤ ℓ → k < 2 ^ ℓa →
    TestOK L XO ℓa ℓ cmc (CMDatU c Da Na rn rd k) c.ap c.nt bt (cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k)
      (cmK d) (cmS c) (cmN c) (cmAr c)

/-- The layout of the gauge block fits `L` and the naturals it writes avoid the register `0`. -/
def GaugeLay.OKU (L : Layout) (g : GaugeLay) : Prop := GaugeLay.OK L g ∧ 0 < g.nt ∧ 0 < g.n0

/-- `GaugeDisj`, and the test block keeps the register `0`. -/
def GaugeDisjU (g : GaugeLay) (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop) : Prop :=
  GaugeDisj g S N Ar ∧ ∀ j, N j → j ≠ 0

/-- The contract of a gauge block uniform in `d`: `GaugeBlockOK` with the layout `GaugeLay.OKU`, the disjointness
`GaugeDisjU` and `d` in the register `0` at the start. -/
def GaugeBlockOKU (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (g : GaugeLay) (gc : XCmdO → XCmdO) : Prop :=
  ∀ (TB : XCmdO) (TDat : Env d → Prop) (T : (Fin d → ℚ) → Bool) (Kt bt : ℕ) (St Nt : ℕ → Prop)
    (Art : ℕ → ℕ → Prop) (σ : Env d) (D : ℤ) (N : Fin d → ℤ) (Da : ℤ) (Na : Fin d → ℤ) (Hn Hd : ℤ) (j b : ℕ),
    LayOK L d ℓa → GaugeLay.OKU L g → 1 ≤ d →
    TestOK L XO ℓa ℓ TB TDat g.atp g.nt bt T Kt St Nt Art → GaugeDisjU g St Nt Art →
    Stable TDat (fun y => gaugeS g y ∨ St y) (fun j => gaugeN g j ∨ Nt j) (fun b k => gaugeAr g b k ∨ Art b k) →
    TDat σ → σ.nat 0 = d →
    σ.arr g.ax 0 = D → (∀ i : Fin d, σ.arr g.ax (1 + (i : ℕ)) = N i) →
    σ.arr g.aa 0 = Da → (∀ i : Fin d, σ.arr g.aa (1 + (i : ℕ)) = Na i) →
    σ.sc g.cHn = Hn → σ.sc g.cHd = Hd → σ.nat g.nj = j → σ.sc g.c2j = 2 ^ j →
    0 < D → 0 < Da → 0 < Hn → 0 < Hd → D < 2 ^ b → (∀ i, |N i| < 2 ^ b) → Da < 2 ^ b → (∀ i, |Na i| < 2 ^ b) →
    Hn < 2 ^ b → Hd < 2 ^ b → 3 * b + j + 2 ≤ bt → bt + 4 ≤ ℓ → j + 1 < 2 ^ ℓa →
    XRunsBO L XO ℓa ℓ (gc TB) σ (gaugeK d j Kt) (fun σ' =>
      σ'.sc g.gout = ((gaugeIt T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j j).2 : ℝ) ∧
        FrameA (fun y => gaugeS g y ∨ St y) (fun j => gaugeN g j ∨ Nt j) (fun b k => gaugeAr g b k ∨ Art b k) σ σ' ∧
        σ'.draws = σ.draws)

/-! ## The code -/

/-- The preamble of the CM block, with the loop bound `n0 + 2 = d` read from the register `0`. -/
def xcmPreU (L : Layout) (c : CMLay) : XCmd :=
  .seq (.prim (.frag (.nconst c.n0 0)))
  (.seq (toX (VL.aget L c.u c.ap c.n0))
  (.seq (toX (VL.aget L (c.u + 1) c.aa c.n0))
  (.seq (toX (VL.sop2 L .mul (c.u + 2) c.c2k c.cr0n))
  (.seq (toX (VL.sop2 L .add (c.u + 3) (c.u + 2) c.cr0d))
  (.seq (toX (VL.sop2 L .add (c.u + 3) (c.u + 3) c.cr0d))
  (.seq (toX (VL.sop2 L .mul (c.u + 3) (c.u + 3) (c.u + 1)))
  (.seq (toX (VL.sop2 L .add (c.u + 4) c.cr0d c.cr0d))
  (.seq (toX (VL.sop2 L .mul (c.u + 4) (c.u + 4) c.u))
  (.seq (toX (VL.sop2 L .mul (c.u + 5) c.u (c.u + 1)))
  (.seq (toX (VL.sop2 L .mul (c.u + 5) (c.u + 5) (c.u + 2)))
  (.seq (toX (VL.aset L c.aq c.n0 (c.u + 5)))
  (.seq (.prim (.frag (.nconst c.n0 1)))
  (.seq (.prim (.frag (.nconst (c.n0 + 2) 0)))
  (.seq (.prim (.frag (.nadd (c.n0 + 2) (c.n0 + 2) 0)))
    (.prim (.frag (.nconst (c.n0 + 3) 1)))))))))))))))))

/-- The CM block uniform in `d`. -/
def xcmU (L : Layout) (c : CMLay) : XCmdO :=
  .seq (.base (.seq (xcmPreU L c) (xcmLoop L c))) (xorcO L c.nt c.aq c.nk)

/-- The preamble of the gauge block, with the loop bound `n0 + 3 = d + 1` read from the register `0`. -/
def xgPreU (L : Layout) (g : GaugeLay) : XCmd :=
  .seq (.prim (.frag (.nconst (g.n0 + 1) 1)))
  (.seq (.prim (.frag (.nconst (g.n0 + 3) 1)))
  (.seq (.prim (.frag (.nadd (g.n0 + 3) (g.n0 + 3) 0)))
  (.seq (.prim (.frag (.nconst (g.n0 + 2) 0)))
  (.seq (toX (VL.aget L (g.u + 4) g.ax (g.n0 + 2)))
  (.seq (toX (VL.aget L (g.u + 5) g.aa (g.n0 + 2)))
  (.seq (toX (VL.sconst L (g.u + 3) ((2 : ℤ) : ℚ)))
  (.seq (toX (VL.sconst L g.u ((0 : ℤ) : ℚ)))
  (.seq (toX (VL.sop2 L .add (g.u + 1) g.c2j g.u))
  (.seq (toX (VL.sop2 L .mul (g.u + 7) g.c2j g.cHd))
    (toX (VL.sop2 L .mul (g.u + 9) (g.u + 7) (g.u + 5))))))))))))

/-- The gauge block uniform in `d`. -/
def xgaugeU (L : Layout) (g : GaugeLay) (TB : XCmdO) : XCmdO :=
  .seq (.base (xgPreU L g))
  (.seq (xforNO g.n0 g.nj (g.n0 + 1) (xgBody L g TB))
    (.base (.seq (toX (VL.sconst L (g.u + 11) ((0 : ℤ) : ℚ))) (toX (VL.sop2 L .add g.gout (g.u + 1) (g.u + 11))))))

/-! ## The CM block -/

set_option maxHeartbeats 4000000 in
theorem cmPreU_runs {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {c : CMLay} (hc : CMLay.OK L c)
    (hd : 1 ≤ d) {σ : Env d} {D Da rn rd : ℤ} {k b bt : ℕ} (hD : σ.arr c.ap 0 = D) (hDa : σ.arr c.aa 0 = Da)
    (hrn : σ.sc c.cr0n = rn) (hrd : σ.sc c.cr0d = rd) (h2k : σ.sc c.c2k = 2 ^ k) (bD : |D| ≤ 2 ^ bt)
    (bDa : |Da| ≤ 2 ^ b) (brn : |rn| ≤ 2 ^ b) (brd : |rd| ≤ 2 ^ b) (hℓ : 2 * b + bt + k + 6 ≤ ℓ) (hn0 : 0 < c.n0) (h0 : σ.nat 0 = d) :
    XRunsB L X ℓa ℓ (xcmPreU L c) σ 19 (fun σ' =>
      σ'.sc (c.u + 3) = cmP Da rn rd k ∧ σ'.sc (c.u + 4) = cmQv D rd ∧ σ'.arr c.aq 0 = cmDq D Da rn k ∧
      σ'.nat c.n0 = 1 ∧ σ'.nat (c.n0 + 2) = d ∧ σ'.nat (c.n0 + 3) = 1 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => c.u ≤ y ∧ y < c.u + 16) (fun j => c.n0 ≤ j ∧ j < c.n0 + 4)
        (fun b' k' => b' = c.aq ∧ k' = 0) σ σ') := by
  obtain ⟨⟨ha, hp, hq⟩, ⟨hqa, hqp⟩, ⟨hs1, hs2, hs3, hs4⟩, ⟨hu1, hu2, hu3⟩, ⟨hn1, hn2, hn3⟩, ⟨hn4, hn5, hn6⟩⟩ := hc
  have hasz : ∀ j ≤ d, j < asz d := fun j hj => by unfold asz; nlinarith
  have hdℓa : d < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; nlinarith) (asz_lt hL ha)
  have h1ℓa : 1 < 2 ^ ℓa := by omega
  have bb : ∀ (z : ℤ) (e : ℕ), |z| ≤ 2 ^ e → e ≤ 2 * b + bt + k + 3 → |z| < 2 ^ ℓ := fun z e hz he =>
    lt_of_le_of_lt (absI_mono hz he) (pow_lt_pow_right₀ (by norm_num) (by omega))
  have m1 := absI_mul_le (bound_two_pow k) brn
  have m2 := absI_add_le m1 (absI_mono brd (by omega : b ≤ k + b))
  have m3 := absI_add_le m2 (absI_mono brd (by omega : b ≤ k + b + 1))
  have m4 := absI_mul_le m3 bDa
  have m5 := absI_add_le brd brd
  have m6 := absI_mul_le m5 bD
  have m7 := absI_mul_le bD bDa
  have m8 := absI_mul_le m7 m1
  have z0 : (0 : ℕ) ≠ c.n0 := by omega
  have r1 : c.cr0n ≠ c.u := by omega
  have r2 : c.cr0d ≠ c.u := by omega
  have r3 : c.c2k ≠ c.u := by omega
  have r1' : ∀ j, c.cr0n ≠ c.u + j := fun j => by omega
  have r2' : ∀ j, c.cr0d ≠ c.u + j := fun j => by omega
  have r3' : ∀ j, c.c2k ≠ c.u + j := fun j => by omega
  refine XV.mono (K := 1 + (2 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (1 + (1 + (1 + 1))))))))))))))) ?_
    le_rfl (fun _ h => h)
  refine XV.seq (XV.nconst hL (i := c.n0) (by omega) 0 (by omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.aget hL (x := c.u) (a := c.ap) (i := c.n0) (by omega) hp (by omega)
    (by simp; exact hasz 0 (by omega))
    (by simpa only [Env.setNat_arr, Env.setNat_nat, ite_true, hD] using XV.abs_int_lt (bb _ _ bD (by omega))))
    fun σ2 e2 => ?_
  subst e2
  simp only [Env.setNat_arr, Env.setNat_nat, ite_true, hD]
  refine XV.seq (XV.aget hL (x := c.u + 1) (a := c.aa) (i := c.n0) (by omega) ha (by omega)
    (by simp; exact hasz 0 (by omega))
    (by simpa only [Env.setSc_arr, Env.setNat_arr, Env.setSc_nat, Env.setNat_nat, ite_true, hDa] using
      XV.abs_int_lt (bb _ _ bDa (by omega)))) fun σ3 e3 => ?_
  subst e3
  simp only [Env.setSc_arr, Env.setNat_arr, Env.setSc_nat, Env.setNat_nat, ite_true, hDa]
  refine XV.seq (XV.mulI hL (x := c.u + 2) (a := c.c2k) (b := c.cr0n) (u := 2 ^ k) (v := rn) (by omega) (by omega)
    (by omega) (by simp [r3, r3', h2k]) (by simp [r1, r1', hrn]) (bb _ _ (bound_two_pow k) (by omega))
    (bb _ _ brn (by omega)) (bb _ _ m1 (by omega))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.addI hL (x := c.u + 3) (a := c.u + 2) (b := c.cr0d) (u := 2 ^ k * rn) (v := rd) (by omega)
    (by omega) (by omega) (by simp) (by simp [r2, r2', hrd]) (bb _ _ m1 (by omega)) (bb _ _ brd (by omega))
    (bb _ _ m2 (by omega))) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.addI hL (x := c.u + 3) (a := c.u + 3) (b := c.cr0d) (u := 2 ^ k * rn + rd) (v := rd)
    (by omega) (by omega) (by omega) (by simp) (by simp [r2, r2', hrd]) (bb _ _ m2 (by omega))
    (bb _ _ brd (by omega)) (bb _ _ m3 (by omega))) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.mulI hL (x := c.u + 3) (a := c.u + 3) (b := c.u + 1) (u := 2 ^ k * rn + rd + rd) (v := Da)
    (by omega) (by omega) (by omega) (by simp) (by simp) (bb _ _ m3 (by omega)) (bb _ _ bDa (by omega))
    (bb _ _ m4 (by omega))) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.addI hL (x := c.u + 4) (a := c.cr0d) (b := c.cr0d) (u := rd) (v := rd) (by omega)
    (by omega) (by omega) (by simp [r2, r2', hrd]) (by simp [r2, r2', hrd]) (bb _ _ brd (by omega))
    (bb _ _ brd (by omega)) (bb _ _ m5 (by omega))) fun σ8 e8 => ?_
  subst e8
  refine XV.seq (XV.mulI hL (x := c.u + 4) (a := c.u + 4) (b := c.u) (u := rd + rd) (v := D) (by omega)
    (by omega) (by omega) (by simp) (by simp) (bb _ _ m5 (by omega)) (bb _ _ bD (by omega))
    (bb _ _ m6 (by omega))) fun σ9 e9 => ?_
  subst e9
  refine XV.seq (XV.mulI hL (x := c.u + 5) (a := c.u) (b := c.u + 1) (u := D) (v := Da) (by omega)
    (by omega) (by omega) (by simp) (by simp) (bb _ _ bD (by omega)) (bb _ _ bDa (by omega))
    (bb _ _ m7 (by omega))) fun σ10 e10 => ?_
  subst e10
  refine XV.seq (XV.mulI hL (x := c.u + 5) (a := c.u + 5) (b := c.u + 2) (u := D * Da) (v := 2 ^ k * rn)
    (by omega) (by omega) (by omega) (by simp) (by simp) (bb _ _ m7 (by omega)) (bb _ _ m1 (by omega))
    (bb _ _ m8 (by omega))) fun σ11 e11 => ?_
  subst e11
  refine XV.seq (XV.aset hL (a := c.aq) (i := c.n0) (x := c.u + 5) hq (by omega) (by omega)
    (by simp; exact hasz 0 (by omega))
    (by rw [Env.setSc_sc, ite_eq_left rfl]; exact XV.abs_int_lt (bb _ _ m8 (by omega)))) fun σ12 e12 => ?_
  subst e12
  refine XV.seq (XV.nconst hL (i := c.n0) (by omega) 1 h1ℓa) fun σ13 e13 => ?_
  subst e13
  refine XV.seq (XV.nconst hL (i := c.n0 + 2) (by omega) 0 (by omega)) fun σ14 e14 => ?_
  subst e14
  refine XV.seq (XV.nadd hL (i := c.n0 + 2) (a := c.n0 + 2) (b := 0) (by omega) (by omega) (by omega)
    (by simp only [Env.setNat_nat, ite_true]; omega) (by simp [z0, h0]; exact hdℓa)) fun σ14' e14' => ?_
  subst e14'
  refine XV.mono (XV.nconst hL (i := c.n0 + 3) (by omega) 1 h1ℓa) le_rfl fun σ15 e15 => ?_
  subst e15
  refine ⟨by simp [cmP], by simp [cmQv], by simp [cmDq], by simp, by simp [z0, h0], by simp, by simp, ?_⟩
  have hS : ∀ y, c.u ≤ y → y < c.u + 16 → c.u ≤ y ∧ y < c.u + 16 := fun y h1 h2 => ⟨h1, h2⟩
  exact (FrameA.refl _ _ _ σ).setNat ⟨le_rfl, by omega⟩ 0 |>.setSc (hS _ le_rfl (by omega)) _
    |>.setSc (hS _ (by omega) (by omega)) _ |>.setSc (hS _ (by omega) (by omega)) _
    |>.setSc (hS _ (by omega) (by omega)) _ |>.setSc (hS _ (by omega) (by omega)) _
    |>.setSc (hS _ (by omega) (by omega)) _ |>.setSc (hS _ (by omega) (by omega)) _
    |>.setSc (hS _ (by omega) (by omega)) _ |>.setSc (hS _ (by omega) (by omega)) _
    |>.setSc (hS _ (by omega) (by omega)) _ |>.setArr ⟨rfl, by simp⟩ _
    |>.setNat ⟨le_rfl, by omega⟩ _ |>.setNat ⟨by omega, by omega⟩ _ |>.setNat ⟨by omega, by omega⟩ _
    |>.setNat ⟨by omega, by omega⟩ _

set_option maxHeartbeats 4000000 in
/-- **UNI-CM on the machine, uniform in `d`**: `xcmU L c` is a test block for `cmQ` at the data of its cells and `d` in the register `0`. -/
theorem cmBlockOKU (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (c : CMLay) : CMBlockOKU L XO ℓa ℓ c (xcmU L c) := by
  intro Da Na rn rd k b bt hL hcU hd hDa0 hrn0 hrd0 hDab hNab hrnb hrdb hℓ hka σ D Nv hdatU hD0 hDb hNvb hD hNv
  obtain ⟨hc, -, hn0⟩ := hcU
  obtain ⟨hdat, h0⟩ := hdatU
  obtain ⟨hDa, hNa, hrn, hrd, hk, h2k⟩ := hdat
  have hc' := hc
  obtain ⟨⟨ha, hp, hq⟩, ⟨hqa, hqp⟩, -, -, ⟨hn1, hn2, hn3⟩, ⟨hn4, hn5, hn6⟩⟩ := hc'
  have bD : |D| ≤ 2 ^ bt := by rw [abs_of_pos hD0]; exact hDb.le
  have bDa : |Da| ≤ 2 ^ b := by rw [abs_of_pos hDa0]; exact hDab.le
  have brn : |rn| ≤ 2 ^ b := by rw [abs_of_pos hrn0]; exact hrnb.le
  have brd : |rd| ≤ 2 ^ b := by rw [abs_of_pos hrd0]; exact hrdb.le
  have m1 := absI_mul_le (bound_two_pow k) brn
  have m2 := absI_add_le m1 (absI_mono brd (by omega : b ≤ k + b))
  have m3 := absI_add_le m2 (absI_mono brd (by omega : b ≤ k + b + 1))
  have bP : |cmP Da rn rd k| ≤ 2 ^ (2 * b + bt + k + 2) := absI_mono (absI_mul_le m3 bDa) (by omega)
  have bQ : |cmQv D rd| ≤ 2 ^ (2 * b + bt + k + 2) := absI_mono (absI_mul_le (absI_add_le brd brd) bD) (by omega)
  have bDq : |cmDq D Da rn k| ≤ 2 ^ (2 * b + bt + k + 2) :=
    absI_mono (absI_mul_le (absI_mul_le bD bDa) m1) (by omega)
  have bNv : ∀ i, |Nv i| ≤ 2 ^ (2 * b + bt + k + 2) := fun i => absI_mono (hNvb i).le (by omega)
  have bNa : ∀ i, |Na i| ≤ 2 ^ (2 * b + bt + k + 2) := fun i => absI_mono (hNab i).le (by omega)
  have bNvP : ∀ i, |Nv i * cmP Da rn rd k| ≤ 2 ^ (2 * b + bt + k + 2) := fun i =>
    absI_mono (absI_mul_le (hNvb i).le (absI_mul_le m3 bDa)) (by omega)
  have bNaQ : ∀ i, |Na i * cmQv D rd| ≤ 2 ^ (2 * b + bt + k + 2) := fun i =>
    absI_mono (absI_mul_le (hNab i).le (absI_mul_le (absI_add_le brd brd) bD)) (by omega)
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ (2 * b + bt + k + 2 + 1) → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) (by omega))
  have hD' : σ.arr c.ap 0 = D := hD
  have hbase : XRunsB L XO.X ℓa ℓ (.seq (xcmPreU L c) (xcmLoop L c)) σ (19 + (d * (10 + 3) + 3)) (fun σ2 =>
      σ2.arr c.aq 0 = cmDq D Da rn k ∧
      (∀ i : Fin d, σ2.arr c.aq (1 + (i : ℕ)) = ((Nv i * cmP Da rn rd k - Na i * cmQv D rd : ℤ) : ℝ)) ∧
      σ2.nat c.nk = k ∧ σ2.draws = σ.draws ∧ FrameA (cmS c) (cmN c) (cmAr c) σ σ2) := by
    refine XV.seq (cmPreU_runs hL hc hd hD' hDa hrn hrd h2k bD bDa brn brd hℓ hn0 h0) fun σ1 h1 => ?_
    obtain ⟨e3, e4, eq0, e0, e2, e1, ed1, F1⟩ := h1
    refine XV.mono (cmLoop_runs hL hc e3 e4 e0 e2 e1
      (fun i => by rw [F1.2.2.1 _ _ (fun h => hqp h.1.symm)]; exact hNv i)
      (fun i => by rw [F1.2.2.1 _ _ (fun h => hqa h.1.symm)]; exact hNa i)
      bP bQ bNv bNa bNvP bNaQ (by omega)) le_rfl fun σ2 ⟨hc2, ed2, F2⟩ => ?_
    refine ⟨by rw [F2.2.2.1 _ _ (fun h => by omega), eq0], hc2, ?_, by rw [ed2, ed1], ?_⟩
    · rw [F2.1 _ (by omega), F1.1 _ (by omega), hk]
    · exact (F1.mono (fun y hy => hy) (fun j hj => Or.inr hj) (fun b' k' h => h.1)).trans
        (F2.mono (fun y hy => by omega) (fun j hj => by omega) (fun b' k' h => h.1))
  refine XVO.mono (XVO.seq (K₂ := d + 3) (XVO.ofX hbase) fun σ2 h2 => ?_) (by unfold cmK; omega)
    (fun _ h => h)
  obtain ⟨hq0, hqi, hnk, hd2, F⟩ := h2
  have hpt : ptArr σ2 c.aq = cmPt (ptDN Da Na) ((rn : ℚ) / rd) k (ptDN D Nv) := by
    funext i
    rw [cmPt_eq D Da rn rd k Nv Na hD0 hDa0 hrn0 hrd0 i]
    simp only [ptArr, hq0, hqi i, Int.floor_intCast]
  refine XVO.mono (XVO.orc hL hd hn2 hq hn1 (by rw [hnk]; omega) (by rw [hnk]; exact hka) ?_) le_rfl
    fun σ3 e3 => ?_
  · intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hq0]; exact XV.abs_int_lt (bb _ (absI_mono bDq (by omega)))
    · obtain ⟨i, hi⟩ : ∃ i : Fin d, 1 + (i : ℕ) = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
      rw [← hi, hqi i]; exact XV.abs_int_lt (bb _ (absI_sub_le (bNvP i) (bNaQ i)))
  · subst e3
    refine ⟨?_, F.setNat (Or.inl rfl) _, by simp [hd2]⟩
    rw [Env.setNat_nat, ite_eq_left rfl, hpt, hnk]
    rfl

/-! ## The gauge block -/

set_option maxHeartbeats 4000000 in
theorem gPreU_runs {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {g : GaugeLay} (hg : GaugeLay.OK L g)
    (hd : 1 ≤ d) {σ : Env d} {D Da Hd : ℤ} {j E : ℕ} (hD : σ.arr g.ax 0 = D) (hDa : σ.arr g.aa 0 = Da)
    (hHd : σ.sc g.cHd = Hd) (h2j : σ.sc g.c2j = 2 ^ j) (b1 : |D| ≤ 2 ^ E) (b2 : |Da| ≤ 2 ^ E)
    (b3 : |Hd| ≤ 2 ^ E) (b4 : (2 : ℤ) ^ j ≤ 2 ^ E) (b5 : |2 ^ j * Hd| ≤ 2 ^ E) (b6 : |2 ^ j * Hd * Da| ≤ 2 ^ E)
    (hE : E + 1 < ℓ) (h0 : σ.nat 0 = d) :
    XRunsB L X ℓa ℓ (xgPreU L g) σ 13 (fun σ' =>
      σ'.sc g.u = ((0 : ℤ) : ℝ) ∧ σ'.sc (g.u + 1) = ((2 ^ j : ℤ) : ℝ) ∧ σ'.sc (g.u + 3) = ((2 : ℤ) : ℝ) ∧
      σ'.sc (g.u + 4) = D ∧ σ'.sc (g.u + 5) = Da ∧ σ'.sc (g.u + 7) = ((2 ^ j * Hd : ℤ) : ℝ) ∧
      σ'.sc (g.u + 9) = ((2 ^ j * Hd * Da : ℤ) : ℝ) ∧ σ'.nat (g.n0 + 1) = 1 ∧ σ'.nat (g.n0 + 3) = d + 1 ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => g.u ≤ y ∧ y < g.u + 16) (fun j => g.n0 ≤ j ∧ j < g.n0 + 4) (fun _ _ => False) σ σ') := by
  obtain ⟨⟨hax, haa, hatp⟩, -, ⟨hs1, hs2, hs3, hs4, hs5⟩, ⟨hu1, hu2, hu3, hu4, -, -, -⟩,
    ⟨hn1, hn2, hn3⟩, -⟩ := hg
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ E → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) (by omega))
  have hasz := asz_lt hL hax
  have h1a : 1 < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; nlinarith) hasz
  have hda : d + 1 < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; nlinarith) hasz
  have h0a : 0 < asz d := by unfold asz; nlinarith
  have b2j : |(2 : ℤ) ^ j| ≤ 2 ^ E := by rw [abs_of_pos (by positivity)]; exact b4
  have btwo : |(2 : ℤ)| < 2 ^ ℓ := by
    rw [abs_of_pos (by norm_num)]
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
  have r2 : g.c2j ≠ g.u := by omega
  have r2' : ∀ k, g.c2j ≠ g.u + k := fun k => by omega
  have r3 : g.cHd ≠ g.u := by omega
  have r3' : ∀ k, g.cHd ≠ g.u + k := fun k => by omega
  refine XV.mono (K := 1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (1 + (1 + 1)))))))))) ?_ le_rfl (fun _ h => h)
  refine XV.seq (XV.nconst hL (i := g.n0 + 1) (by omega) 1 h1a) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.nconst hL (i := g.n0 + 3) (by omega) 1 h1a) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nadd hL (i := g.n0 + 3) (a := g.n0 + 3) (b := 0) (by omega) (by omega) (by omega)
    (by simp only [Env.setNat_nat, ite_true]; exact h1a) (by simp [h0]; omega)) fun σ2' e2' => ?_
  subst e2'
  refine XV.seq (XV.nconst hL (i := g.n0 + 2) (by omega) 0 (by omega)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.aget hL (x := g.u + 4) (a := g.ax) (i := g.n0 + 2) (by omega) hax (by omega)
    (by simp; exact h0a) (by simpa [hD] using XV.abs_int_lt (bb _ b1))) fun σ4 e4 => ?_
  subst e4
  simp only [Env.setNat_arr, Env.setNat_nat, ite_true, hD, show g.n0 + 2 ≠ g.n0 + 3 by omega,
    show g.n0 + 2 ≠ g.n0 + 1 by omega, ite_false]
  refine XV.seq (XV.aget hL (x := g.u + 5) (a := g.aa) (i := g.n0 + 2) (by omega) haa (by omega)
    (by simp; exact h0a) (by simpa [hDa] using XV.abs_int_lt (bb _ b2))) fun σ5 e5 => ?_
  subst e5
  simp only [Env.setSc_arr, Env.setNat_arr, Env.setSc_nat, Env.setNat_nat, ite_true, hDa]
  refine XV.seq (XV.constI hL (x := g.u + 3) (by omega) 2 btwo) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.constI hL (x := g.u) (by omega) 0 (by simp)) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.addI hL (x := g.u + 1) (a := g.c2j) (b := g.u) (u := 2 ^ j) (v := 0) (by omega) (by omega)
    (by omega) (by simp [r2, r2', h2j]) (by simp) (bb _ b2j) (by simp) (by simpa using bb _ b2j))
    fun σ8 e8 => ?_
  subst e8
  refine XV.seq (XV.mulI hL (x := g.u + 7) (a := g.c2j) (b := g.cHd) (u := 2 ^ j) (v := Hd) (by omega) (by omega)
    (by omega) (by simp [r2, r2', h2j]) (by simp [r3, r3', hHd]) (bb _ b2j) (bb _ b3) (bb _ b5)) fun σ9 e9 => ?_
  subst e9
  refine XV.mono (XV.mulI hL (x := g.u + 9) (a := g.u + 7) (b := g.u + 5) (u := 2 ^ j * Hd) (v := Da) (by omega)
    (by omega) (by omega) (by simp) (by simp) (bb _ b5) (bb _ b2) (bb _ b6)) le_rfl fun σ10 e10 => ?_
  subst e10
  refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp [h0]; omega, by simp, ?_⟩
  exact (FrameA.refl (fun y => g.u ≤ y ∧ y < g.u + 16) (fun j => g.n0 ≤ j ∧ j < g.n0 + 4) (fun _ _ => False) σ).setNat
    ⟨by omega, by omega⟩ _ |>.setNat ⟨by omega, by omega⟩ _ |>.setNat ⟨by omega, by omega⟩ _
    |>.setNat ⟨by omega, by omega⟩ _
    |>.setSc ⟨by omega, by omega⟩ _ |>.setSc ⟨by omega, by omega⟩ _ |>.setSc ⟨by omega, by omega⟩ _
    |>.setSc ⟨le_rfl, by omega⟩ _ |>.setSc ⟨by omega, by omega⟩ _ |>.setSc ⟨by omega, by omega⟩ _
    |>.setSc ⟨by omega, by omega⟩ _

set_option maxHeartbeats 16000000 in
/-- **UNI-GAUGE on the machine, uniform in `d`**: `xgaugeU L g` meets the contract of the gauge block with `d` in the
register `0`. -/
theorem gaugeBlockOKU (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (g : GaugeLay) :
    GaugeBlockOKU L XO ℓa ℓ g (xgaugeU L g) := by
  intro TB TDat T Kt bt St Nt Art σ D N Da Na Hn Hd j b hL hgU hd hTB hDisjU hStab hdat h0d hD hN hDa hNa hHn hHd hnj
    h2j hD0 hDa0 hHn0 hHd0 hDb hNb hDab hNab hHnb hHdb hbt hℓ hja
  obtain ⟨hg, -, -⟩ := hgU
  obtain ⟨hDisj, -⟩ := hDisjU
  have hg' := hg
  obtain ⟨⟨hax, haa, hatp⟩, ⟨htx, hta⟩, ⟨hs1, hs2, hs3, hs4, hs5⟩, ⟨hu1, hu2, hu3, hu4, hg1, hg2, hg3⟩,
    ⟨hn1, hn2, hn3⟩, ⟨hn4, hn5, hn6⟩⟩ := hg'
  obtain ⟨dS, dN, dA⟩ := hDisj
  have hasz := asz_lt hL hax
  have h1a : 1 < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; nlinarith) hasz
  -- the cells the block and its test keep
  have kHn : ¬ (gaugeS g g.cHn ∨ St g.cHn) := fun h => h.elim (fun h' => by unfold gaugeS at h'; omega)
    (fun h' => (dS _ h').1 rfl)
  have kHd : ¬ (gaugeS g g.cHd ∨ St g.cHd) := fun h => h.elim (fun h' => by unfold gaugeS at h'; omega)
    (fun h' => (dS _ h').2.1 rfl)
  have k2j : ¬ (gaugeS g g.c2j ∨ St g.c2j) := fun h => h.elim (fun h' => by unfold gaugeS at h'; omega)
    (fun h' => (dS _ h').2.2.1 rfl)
  have kj : ¬ (gaugeN g g.nj ∨ Nt g.nj) := fun h => h.elim (fun h' => by unfold gaugeN at h'; omega)
    (fun h' => (dN _ h').1 rfl)
  have kx : ∀ k, ¬ (gaugeAr g g.ax k ∨ Art g.ax k) := fun k h => h.elim (fun h' => htx h'.symm)
    (fun h' => (dA _ _ h').1 rfl)
  have ka : ∀ k, ¬ (gaugeAr g g.aa k ∨ Art g.aa k) := fun k h => h.elim (fun h' => hta h'.symm)
    (fun h' => (dA _ _ h').2.1 rfl)
  have kSt : ∀ y, g.u ≤ y → y < g.u + 16 → ¬ St y := fun y h1 h2 h => (dS _ h).2.2.2.2 ⟨h1, h2⟩
  have kNt : ∀ i, g.n0 ≤ i → i < g.n0 + 4 → ¬ Nt i := fun i h1 h2 h => (dN _ h).2 ⟨h1, h2⟩
  -- bounds
  have bD : |D| ≤ 2 ^ b := by rw [abs_of_pos hD0]; exact hDb.le
  have bDa : |Da| ≤ 2 ^ b := by rw [abs_of_pos hDa0]; exact hDab.le
  have bHn : |Hn| ≤ 2 ^ b := by rw [abs_of_pos hHn0]; exact hHnb.le
  have bHd : |Hd| ≤ 2 ^ b := by rw [abs_of_pos hHd0]; exact hHdb.le
  have bB : |2 ^ j * Hd| ≤ 2 ^ (j + b) := absI_mul_le (bound_two_pow j) bHd
  have bβ : |2 ^ j * Hd * Da| ≤ 2 ^ (j + b + b) := absI_mul_le bB bDa
  have bbE : ∀ z : ℤ, ∀ e, |z| ≤ 2 ^ e → e ≤ 3 * b + j + 1 → |z| < 2 ^ ℓ := fun z e hz he =>
    lt_of_le_of_lt (absI_mono hz he) (pow_lt_pow_right₀ (by norm_num) (by omega))
  refine XVO.mono (K := 13 + ((j * ((12 * d + 17 + Kt) + 3) + 3) + (1 + 1))) ?_
    (by unfold gaugeK; nlinarith [Nat.zero_le (j * Kt), Nat.zero_le (j * d)]) (fun _ h => h)
  refine XVO.seq (XVO.ofX (gPreU_runs (E := 3 * b + j) hL hg hd hD hDa hHd h2j (absI_mono bD (by omega))
    (absI_mono bDa (by omega)) (absI_mono bHd (by omega)) (pow_le_pow_right₀ (by norm_num) (by omega))
    (absI_mono bB (by omega)) (absI_mono bβ (by omega)) (by omega) h0d)) fun σ1 h1 => ?_
  obtain ⟨p0, p1, p3, p4, p5, p7, p9, pone, pd1, pdr, pF⟩ := h1
  have pF' : FrameA (fun y => gaugeS g y ∨ St y) (fun j => gaugeN g j ∨ Nt j) (fun b k => gaugeAr g b k ∨ Art b k)
      σ σ1 :=
    pF.mono (fun y hy => Or.inl (Or.inr hy)) (fun j hj => Or.inl (Or.inr hj)) (fun _ _ h => h.elim)
  refine XVO.seq (XVO.forN hL (i := g.n0) (n := g.nj) (one := g.n0 + 1) (body := xgBody L g TB) (by omega) hn1
    (by omega) (by omega) (by omega) j (12 * d + 17 + Kt) (by omega)
    (fun t σ' => σ'.sc g.u = (((gaugeIt T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j t).1 : ℤ) : ℝ) ∧
      σ'.sc (g.u + 1) = (((gaugeIt T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j t).2 : ℤ) : ℝ) ∧
      σ'.sc (g.u + 3) = ((2 : ℤ) : ℝ) ∧ σ'.sc (g.u + 4) = D ∧ σ'.sc (g.u + 5) = Da ∧
      σ'.sc (g.u + 7) = ((2 ^ j * Hd : ℤ) : ℝ) ∧ σ'.sc (g.u + 9) = ((2 ^ j * Hd * Da : ℤ) : ℝ) ∧
      σ'.nat (g.n0 + 3) = d + 1 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => gaugeS g y ∨ St y) (fun j => gaugeN g j ∨ Nt j) (fun b k => gaugeAr g b k ∨ Art b k) σ σ')
    σ1 (by rw [pF.1 _ (by omega), hnj]) pone ?_ ?_) fun σ2 h2 => ?_
  -- the start of the loop
  · refine ⟨by simp [gaugeIt, p0], by simp [gaugeIt, p1], by simp [p3], by simp [p4], by simp [p5], by simp [p7],
      by simp [p9], by simp [pd1], by simp [pdr], pF'.setNat (Or.inl (Or.inr ⟨le_rfl, by omega⟩)) 0⟩
  -- one turn
  · intro t ht σ' hJ hct hcj hc1
    obtain ⟨jl, ju, j3, j4, j5, j7, j9, jd1, jdr, jF⟩ := hJ
    obtain ⟨hinv, -, -⟩ := gaugeIt_inv T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j t ht.le
    obtain ⟨hle, hup⟩ := gaugeIt_le T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j t ht.le
    set l := (gaugeIt T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j t).1 with hl
    set u := (gaugeIt T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j t).2 with hu
    have hjt : j - t = (j - t - 1) + 1 := by omega
    have hP : 1 ≤ 2 ^ (j - t - 1) := Nat.one_le_two_pow
    rw [hjt, pow_succ] at hinv
    set m := (l + u) / 2 with hm
    have hm1 : 1 ≤ m := by omega
    have hmu : m ≤ u := by omega
    have hmZ : ((l : ℤ) + (u : ℤ)) / 2 = (m : ℤ) := by rw [hm]; omega
    have hmpos : (0 : ℤ) < m := by exact_mod_cast hm1
    -- the data at the start of the turn
    have eHn : σ'.sc g.cHn = Hn := by rw [jF.2.1 _ kHn, hHn]
    have eNx : ∀ i : Fin d, σ'.arr g.ax (1 + (i : ℕ)) = N i := fun i => by rw [jF.2.2.1 _ _ (kx _), hN i]
    have eNa : ∀ i : Fin d, σ'.arr g.aa (1 + (i : ℕ)) = Na i := fun i => by rw [jF.2.2.1 _ _ (ka _), hNa i]
    -- bounds of the turn
    have bl : |(l : ℤ)| ≤ 2 ^ j := by
      rw [abs_of_nonneg (by positivity)]; exact_mod_cast hle.trans hup
    have bu : |(u : ℤ)| ≤ 2 ^ j := by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hup
    have bm : |(m : ℤ)| ≤ 2 ^ j := by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hmu.trans hup
    have blu := absI_add_le bl bu
    have bA : |Hn * m| ≤ 2 ^ (b + j) := absI_mul_le bHn bm
    have bAB : |Hn * m - 2 ^ j * Hd| ≤ 2 ^ (b + j) := by
      have h1 : 0 ≤ Hn * (m : ℤ) := by positivity
      have h2 : 0 ≤ (2 : ℤ) ^ j * Hd := by positivity
      rw [abs_of_nonneg h1] at bA
      rw [abs_of_nonneg h2, show j + b = b + j by ring] at bB
      rw [abs_sub_le_iff]; constructor <;> linarith
    have bα := absI_mul_le bAB bD
    have bDD := absI_mul_le bD bDa
    have bD' := absI_mul_le bDD bA
    have bNα : ∀ i, |Na i * ((Hn * m - 2 ^ j * Hd) * D)| ≤ 2 ^ (b + (b + j + b)) := fun i =>
      absI_mul_le (hNab i).le bα
    have bNβ : ∀ i, |N i * (2 ^ j * Hd * Da)| ≤ 2 ^ (b + (j + b + b)) := fun i => absI_mul_le (hNb i).le bβ
    have bN' : ∀ i, |Na i * ((Hn * m - 2 ^ j * Hd) * D) + N i * (2 ^ j * Hd * Da)| ≤ 2 ^ (3 * b + j + 1) :=
      fun i => by
        have := absI_add_le (absI_mono (bNα i) (by omega : b + (b + j + b) ≤ 3 * b + j))
          (absI_mono (bNβ i) (by omega : b + (j + b + b) ≤ 3 * b + j))
        exact this
    -- the counter and the ray point
    have hbase : XRunsB L XO.X ℓa ℓ (.seq (toX (VL.sop2 L .add (g.u + 2) g.u (g.u + 1)))
        (.seq (xsidiv L (g.u + 2) (g.u + 2) (g.u + 3)) (xgPt L g))) σ' (1 + (1 + (9 + (d * (10 + 2) + 2))))
        (fun σ3 => σ3.arr g.atp 0 = ((D * Da * (Hn * m) : ℤ) : ℝ) ∧
          (∀ i : Fin d, σ3.arr g.atp (1 + (i : ℕ)) =
            ((Na i * ((Hn * m - 2 ^ j * Hd) * D) + N i * (2 ^ j * Hd * Da) : ℤ) : ℝ)) ∧
          σ3.draws = σ'.draws ∧
          FrameA (fun y => y = g.u + 2 ∨ gPtS g y) (fun j => j = g.n0 + 2) (fun b _ => b = g.atp) σ' σ3) := by
      refine XV.seq (XV.addI hL (x := g.u + 2) (a := g.u) (b := g.u + 1) (u := l) (v := u) (by omega) (by omega)
        (by omega) jl ju (bbE _ _ bl (by omega)) (bbE _ _ bu (by omega)) (bbE _ _ blu (by omega)))
        fun σa ea => ?_
      subst ea
      refine XV.seq (XV.divI hL (x := g.u + 2) (a := g.u + 2) (b := g.u + 3) (u := l + u) (v := 2) (by omega)
        (by omega) (by omega) (by simp) (by simp [j3]) (bbE _ _ blu (by omega))
        (bbE _ 1 (by norm_num) (by omega))) fun σb eb => ?_
      subst eb
      refine XV.mono (gPt_runs (E := 3 * b + j) (m := (m : ℤ)) (Hn := Hn) (D := D) (Da := Da) (B := 2 ^ j * Hd)
        (β := 2 ^ j * Hd * Da) (N := N) (Na := Na) hL hg hd
        (by rw [Env.setSc_sc, ite_eq_left rfl, hmZ]) (by simp [show g.cHn ≠ g.u + 2 by omega, eHn])
        (by simp [j4]) (by simp [j5]) (by simp [j7]) (by simp [j9]) (by simp [hc1]) (by simp [jd1])
        (fun i => by simp [eNx i]) (fun i => by simp [eNa i]) (absI_mono bm (by omega)) (absI_mono bHn (by omega))
        (absI_mono bD (by omega)) (absI_mono bDa (by omega)) (absI_mono bB (by omega)) (absI_mono bβ (by omega))
        (absI_mono bA (by omega)) (absI_mono bAB (by omega)) (absI_mono bα (by omega)) (absI_mono bDD (by omega))
        (absI_mono bD' (by omega)) (fun i => absI_mono (hNab i).le (by omega))
        (fun i => absI_mono (hNb i).le (by omega)) (fun i => absI_mono (bNα i) (by omega))
        (fun i => absI_mono (bNβ i) (by omega)) (by omega)) le_rfl fun σ3 ⟨h3a, h3b, h3d, F3⟩ => ?_
      refine ⟨h3a, h3b, by rw [h3d]; simp, ?_⟩
      exact ((FrameA.refl (fun y => y = g.u + 2 ∨ gPtS g y) (fun j => j = g.n0 + 2) (fun b _ => b = g.atp) σ').setSc
        (Or.inl rfl) _ |>.setSc (Or.inl rfl) _).trans (F3.mono (fun y hy => Or.inr hy) (fun j hj => hj)
          (fun b k h => h))
    refine XVO.mono (K := (1 + (1 + (9 + (d * (10 + 2) + 2)))) + (Kt + (2 + 2))) ?_ (by omega) (fun _ h => h)
    refine XVO.seq (XVO.ofX hbase) fun σ3 h3 => ?_
    obtain ⟨h3a, h3b, h3d, F3⟩ := h3
    have F3u : FrameA (fun y => gaugeS g y ∨ St y) (fun j => gaugeN g j ∨ Nt j)
        (fun b k => gaugeAr g b k ∨ Art b k) σ σ3 :=
      jF.trans (F3.mono (fun y hy => Or.inl (by unfold gaugeS gPtS at *; omega))
        (fun i hi => Or.inl (by unfold gaugeN; omega)) (fun b k h => Or.inl h))
    have hTD : TDat σ3 := hStab σ σ3 hdat F3u (by rw [h3d, jdr])
    have hD'0 : 0 < D * Da * (Hn * m) := mul_pos (mul_pos hD0 hDa0) (mul_pos hHn0 hmpos)
    refine XVO.seq (hTB σ3 (D * Da * (Hn * m))
      (fun i => Na i * ((Hn * m - 2 ^ j * Hd) * D) + N i * (2 ^ j * Hd * Da)) hTD hD'0
      (lt_of_le_of_lt (le_abs_self _ |>.trans (absI_mono bD' (by omega : b + b + (b + j) ≤ 3 * b + j)))
        (pow_lt_pow_right₀ (by norm_num) (by omega)))
      (fun i => lt_of_le_of_lt (bN' i) (pow_lt_pow_right₀ (by norm_num) (by omega))) h3a h3b) fun σ4 h4 => ?_
    obtain ⟨hnt, F4, d4⟩ := h4
    have hpt : ptDN (D * Da * (Hn * m)) (fun i => Na i * ((Hn * m - 2 ^ j * Hd) * D) + N i * (2 ^ j * Hd * Da)) =
        gaugePt (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j m := by
      funext i
      rw [gaugePt_eq Hn Hd D Da j m N Na hHn0 hHd0 hD0 hDa0 hm1 i]
      rfl
    rw [hpt] at hnt
    -- what the turn keeps
    have k4n : ∀ i, ¬ Nt i → i ≠ g.n0 + 2 → σ4.nat i = σ'.nat i := fun i h1 h2 => by
      rw [F4.1 _ h1, F3.1 _ h2]
    have k4s : ∀ y, ¬ St y → ¬ (y = g.u + 2 ∨ gPtS g y) → σ4.sc y = σ'.sc y := fun y h1 h2 => by
      rw [F4.2.1 _ h1, F3.2.1 _ h2]
    have e41 : σ4.nat (g.n0 + 1) = 1 := by rw [k4n _ (kNt _ (by omega) (by omega)) (by omega), hc1]
    have e4l : σ4.sc g.u = ((l : ℤ) : ℝ) := by
      rw [k4s _ (kSt _ le_rfl (by omega)) (by unfold gPtS; omega), jl]
    have e4u : σ4.sc (g.u + 1) = ((u : ℤ) : ℝ) := by
      rw [k4s _ (kSt _ (by omega) (by omega)) (by unfold gPtS; omega), ju]
    have e43 : σ4.sc (g.u + 3) = ((2 : ℤ) : ℝ) := by
      rw [k4s _ (kSt _ (by omega) (by omega)) (by unfold gPtS; omega), j3]
    have e44 : σ4.sc (g.u + 4) = D := by rw [k4s _ (kSt _ (by omega) (by omega)) (by unfold gPtS; omega), j4]
    have e45 : σ4.sc (g.u + 5) = Da := by rw [k4s _ (kSt _ (by omega) (by omega)) (by unfold gPtS; omega), j5]
    have e47 : σ4.sc (g.u + 7) = ((2 ^ j * Hd : ℤ) : ℝ) := by
      rw [k4s _ (kSt _ (by omega) (by omega)) (by unfold gPtS; omega), j7]
    have e49 : σ4.sc (g.u + 9) = ((2 ^ j * Hd * Da : ℤ) : ℝ) := by
      rw [k4s _ (kSt _ (by omega) (by omega)) (by unfold gPtS; omega), j9]
    have e4d1 : σ4.nat (g.n0 + 3) = d + 1 := by
      rw [k4n _ (kNt _ (by omega) (by omega)) (by omega), jd1]
    have e4c : σ4.nat g.n0 = t := by rw [k4n _ (kNt _ le_rfl (by omega)) (by omega), hct]
    have e4j : σ4.nat g.nj = j := by rw [k4n _ (fun h => (dN _ h).1 rfl) (by omega), hcj]
    have F4u : FrameA (fun y => gaugeS g y ∨ St y) (fun j => gaugeN g j ∨ Nt j)
        (fun b k => gaugeAr g b k ∨ Art b k) σ σ4 :=
      F3u.trans (F4.mono (fun y hy => Or.inr hy) (fun i hi => Or.inr hi) (fun b k h => Or.inr h))
    have hd4 : σ4.draws = σ.draws := by rw [d4, h3d, jdr]
    have e4t : σ4.nat g.nt < 2 ^ ℓa := by rw [hnt]; split_ifs <;> omega
    by_cases hT : T (gaugePt (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j m) = true
    · -- an accept: `u := m`
      have hnt1 : σ4.nat g.nt = 1 := by rw [hnt, ite_eq_left hT]
      refine XVO.ifN_f hL hn2 (by omega) e4t (by rw [e41]; exact h1a) (by rw [hnt1, e41]; omega) ?_
      refine XVO.ofX (XV.seq (K₂ := 1) (XV.addI hL (x := g.u + 1) (a := g.u) (b := g.u + 1) (u := l) (v := u)
        (by omega) (by omega) (by omega) e4l e4u (bbE _ _ bl (by omega)) (bbE _ _ bu (by omega))
        (bbE _ _ blu (by omega)))
        fun σ5 e5 => ?_)
      subst e5
      refine XV.mono (XV.divI hL (x := g.u + 1) (a := g.u + 1) (b := g.u + 3) (u := l + u) (v := 2) (by omega)
        (by omega) (by omega) (by simp) (by simp [e43]) (bbE _ _ blu (by omega))
        (bbE _ 1 (by norm_num) (by omega))) le_rfl fun σ6 e6 => ?_
      subst e6
      refine ⟨by simp [e4c], by simp [e4j], by simp [e41], ?_⟩
      rw [gaugeIt_succ, ← hl, ← hu, ← hm, ite_eq_left hT]
      refine ⟨by simp [e4l], by simp [hmZ], by simp [e43], by simp [e44], by simp [e45], by simp [e47],
        by simp [e49], by simp [e4d1], by simp [hd4], ?_⟩
      exact F4u.setSc (Or.inl (Or.inr ⟨by omega, by omega⟩)) _ |>.setSc (Or.inl (Or.inr ⟨by omega, by omega⟩)) _
        |>.setNat (Or.inl (Or.inr ⟨le_rfl, by omega⟩)) _
    · -- a reject: `l := m`
      have hnt0 : σ4.nat g.nt = 0 := by rw [hnt, ite_eq_right hT]
      refine XVO.mono (XVO.ifN_t (K := 2) hL hn2 (by omega) e4t (by rw [e41]; exact h1a) (by rw [hnt0, e41]; omega) ?_)
        (by omega) (fun _ h => h)
      refine XVO.ofX (XV.seq (K₂ := 1) (XV.addI hL (x := g.u) (a := g.u) (b := g.u + 1) (u := l) (v := u)
        (by omega) (by omega) (by omega) e4l e4u (bbE _ _ bl (by omega)) (bbE _ _ bu (by omega))
        (bbE _ _ blu (by omega)))
        fun σ5 e5 => ?_)
      subst e5
      refine XV.mono (XV.divI hL (x := g.u) (a := g.u) (b := g.u + 3) (u := l + u) (v := 2) (by omega)
        (by omega) (by omega) (by simp) (by simp [e43]) (bbE _ _ blu (by omega))
        (bbE _ 1 (by norm_num) (by omega))) le_rfl fun σ6 e6 => ?_
      subst e6
      refine ⟨by simp [e4c], by simp [e4j], by simp [e41], ?_⟩
      rw [gaugeIt_succ, ← hl, ← hu, ← hm, ite_eq_right hT]
      refine ⟨by simp [hmZ], by simp [e4u], by simp [e43], by simp [e44], by simp [e45], by simp [e47],
        by simp [e49], by simp [e4d1], by simp [hd4], ?_⟩
      exact F4u.setSc (Or.inl (Or.inr ⟨le_rfl, by omega⟩)) _ |>.setSc (Or.inl (Or.inr ⟨le_rfl, by omega⟩)) _
        |>.setNat (Or.inl (Or.inr ⟨le_rfl, by omega⟩)) _
  -- the output
  · obtain ⟨⟨-, q1, -, -, -, -, -, -, qdr, qF⟩, -, -, -⟩ := h2
    refine XVO.ofX (XV.seq (XV.constI hL (x := g.u + 11) (by omega) 0 (by simp)) fun σ5 e5 => ?_)
    subst e5
    have bj : |(((gaugeIt T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j j).2 : ℕ) : ℤ)| ≤ 2 ^ j := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast (gaugeIt_le T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j j le_rfl).2
    refine XV.mono (XV.addI hL (x := g.gout) (a := g.u + 1) (b := g.u + 11)
      (u := ((gaugeIt T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j j).2 : ℤ)) (v := 0) hs4 (by omega) (by omega)
      (by simp [q1]) (by simp) (bbE _ _ bj (by omega)) (by simp) (by simpa using bbE _ _ bj (by omega))) le_rfl
      fun σ6 e6 => ?_
    subst e6
    refine ⟨by simp, ?_, by simp [qdr]⟩
    exact qF.setSc (Or.inl (Or.inr ⟨by omega, by omega⟩)) _ |>.setSc (Or.inl (Or.inl rfl)) _

end AdversarialBco.Uni
