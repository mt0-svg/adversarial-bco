/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSetupAll
public import AdversarialBco.UW.ProgMachBL

@[expose] public section

/-!
# BL-OW's setup on the oracle machine

`SetupSpecW` (UW/ProgMachBL.lean) from BL-O's six setup contracts (Unified/ProgOSetup.lean) and PARAM-W's contract
`ParamWSpecS`. The setup `xinitW` is BL-O's `xinitO` with PARAM-W run after the cross check and the two
thresholds stored at the end:

1. `xpreW`: P0, PARAM at `k_δ`, `sZ := 0` (BL-O's), then `k_δ` copied from `sKd` into `sDmu` (the cross check writes
   its flag into `sKd`, and only the epoch start writes `sDmu`), then TRI-OGD-O, the coin count and the cross check
   (BL-O's: they read PARAM's values at `parO`). The state it leaves: `PreW`.
2. `xpostW`: `xparkW` (the flag into the slot `125`, `k_δ` back into `sKd`, `d` into the slot `0`, where PARAM-W reads
   them as PARAM does); PARAM-W (`ParO` at `parOW`, `2^p b0`, `2^p y0` in the slots `122`, `123`); `xunparkW` (`0`
   into the slot `0`, the flag back into `sKd`); the epoch start (v2.1's, it reads `A_0`, `B_0` at `parOW`); the mode
   (BL-O's); `xcellsW` (`2^p b0`, `2^p y0` into `aMuS[d]`, `aAS[d·d]`).

The invariant before `xcellsW` is `bloInv_mk` at `cfgWW` (BL-O's lemma: it reads the configuration's fields only through
the cells); `xcellsW` keeps it (`BLInv.cellsW`) and gives `CellsW`. The cross check runs at `cfgS` on PARAM's values,
and its verdict is the one at `cfgWW` (`crossOK_cfgS_cfgWW`: the check reads `p` and `R`, which `parOW` keeps).

* `setupSpecW_of`: `SetupSpecW` for `xinitW` from the seven contracts, at the constants `csO`, `ksO` of BL-O's setup with
  PARAM-W's constants added to PARAM's and `11` units for the new moves;
* `progSetupW`: `ProgSetupW` from PARAM-W's contract, with BL-O's six proved contracts.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.UW.BLOW (cfgWW cfgOW modeOW b0OW y0OW parOW parOW_p parOW_R)
open AdversarialBco.Bit.BLP (Cfg Mode St Par init up rnd)
open BitRAM BitRAMO

variable {d : ℕ}

/-! ## PARAM-W's contract -/

/-- **PARAM-W's contract**: from `ParamSpecO`'s cells (`d` in `rD` and the slot `0`, `1` in `rOne`, `0`
in the mode slot, `n` in `sN`, `1, 2, 4` in the slots `26, 27, 28`, `k_δ` in `sKd`), `xpw L` writes PARAM's values at
`parOW d n δ` (`ParO`), `2^p b0` and `2^p y0` into the slots `122`, `123`, integers at most `2^{C (W + 1)^k}`, within
`C (W + 1)^k` units, in PARAM's frame; it reads no coin. -/
def ParamWSpecS (xpw : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ) (σ : Env d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA →
    σ.nat rD = d → σ.nat rOne = 1 → σ.sc 0 = d → σ.sc sMode = 0 → σ.sc sN = n → σ.sc 26 = 1 → σ.sc 27 = 2 →
    σ.sc 28 = 4 → σ.sc sKd = kDel δ →
    C * (wU d n δ r0 R0 a + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xpw L) σ (C * (wU d n δ r0 R0 a + 1) ^ k) (fun σ' =>
      ParO σ' (parOW d n δ) ∧ SlotBnd σ' 4 22 (C * (wU d n δ r0 R0 a + 1) ^ k) ∧
      σ'.sc 122 = ((qn (parO d n δ).p (b0OW d n δ) : ℤ) : ℝ) ∧
      σ'.sc 123 = ((qn (parO d n δ).p (y0OW d n δ) : ℤ) : ℝ) ∧
      |qn (parO d n δ).p (b0OW d n δ)| ≤ 2 ^ (C * (wU d n δ r0 R0 a + 1) ^ k) ∧
      |qn (parO d n δ).p (y0OW d n δ)| ≤ 2 ^ (C * (wU d n δ r0 R0 a + 1) ^ k) ∧ σ'.draws = σ.draws ∧
      FrameA SPar (fun j => rP ≤ j) (fun b _ => 8 ≤ b) σ σ')

theorem ParamWSpecS.room {x : Layout → XCmdO} {C k nS nN nA nS' nN' nA' : ℕ} (h : ParamWSpecS x C k nS nN nA)
    (hS : nS ≤ nS') (hN : nN ≤ nN') (hA : nA ≤ nA') : ParamWSpecS x C k nS' nN' nA' :=
  fun d L w n δ r0 R0 a ℓa ℓ σ hI hL hR => h d L w n δ r0 R0 a ℓa ℓ σ hI hL (hR.mono hS hN hA)

/-! ## Facts on BL-OW's configuration -/

/-- `1/2 < ε'` on the grid `2^{-pF}`: PARAM-W rounds `ε'` up. -/
theorem parOW_half_iff (d n : ℕ) (δ : ℚ) :
    1 / 2 < (parOW d n δ).eps ↔ (2 : ℤ) ^ (parOW d n δ).pF < 2 * qn (parOW d n δ).pF (parOW d n δ).eps :=
  half_lt_up_iff _ _

theorem parOW_onG_A0 (d n : ℕ) (δ : ℚ) : OnG (parOW d n δ).p (parOW d n δ).A0 := onG_rnd_s _ _

theorem parOW_onG_B0 (d n : ℕ) (δ : ℚ) : OnG (parOW d n δ).p (parOW d n δ).B0 := onG_rnd_s _ _

/-- The cross check reads the configuration's `p`, `R`, `a`, `r0`, `R0` and position only. -/
theorem crossOK_congr (orc : (Fin d → ℚ) → ℕ → Bool) {c c' : CfgO d} (hp : c.par.p = c'.par.p)
    (hR : c.par.R = c'.par.R) (ha : c.a = c'.a) (hr : c.r0 = c'.r0) (hR0 : c.R0 = c'.R0) (hm : c.μS = c'.μS)
    (hA : c.AS = c'.AS) : crossOK orc c ↔ crossOK orc c' := by
  unfold crossOK CfgO.T CfgO.kC CfgO.kK
  rw [hp, hR, ha, hr, hR0, hm, hA]

/-- **The cross check on PARAM's values is the one of BL-OW's configuration**: `parOW` keeps `parO`'s `p` and `R`. -/
theorem crossOK_cfgS_cfgWW (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : WorldO d) :
    crossOK w.orc (cfgS n δ r0 R0 a ((cfgWW d n δ r0 R0 a w).μS, (cfgWW d n δ r0 R0 a w).AS)) ↔
      crossOK w.orc (cfgWW d n δ r0 R0 a w) :=
  crossOK_congr w.orc (parOW_p d n δ).symm (parOW_R d n δ).symm rfl rfl rfl rfl rfl

/-- `k_δ < W`. -/
theorem kDel_lt_wU {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hI : InU d n δ r0 R0) : kDel δ < wU d n δ r0 R0 a := by
  have hk := kDel_le_size hI.hδ0
  have hS : len (δ.den : ℤ) ≤ sizeN δ r0 R0 a := by unfold sizeN; omega
  rw [len_natCast δ.den] at hS
  unfold wU
  omega

/-! ## The new moves -/

/-- `k_δ` into `sDmu` (`sZ = 0`). -/
def xstashW (L : Layout) : XCmd := toX (VL.sop2 L .add sDmu sKd sZ)

/-- The flag into the slot `125`, `k_δ` back into `sKd`, `d` into the slot `0` (`sZ = 0`). -/
def xparkW (L : Layout) : XCmd :=
  .seq (toX (VL.sop2 L .add 125 sKd sZ)) (.seq (toX (VL.sop2 L .add sKd sDmu sZ)) (toX (VL.ncast L 0 rD)))

/-- `0` into the slot `0`, the flag back into `sKd`. -/
def xunparkW (L : Layout) : XCmd :=
  .seq (toX (VL.sconst L sZ 0)) (toX (VL.sop2 L .add sKd 125 sZ))

/-- The slots `122`, `123` into `aMuS[d]`, `aAS[d·d]`. -/
def xcellsW (L : Layout) : XCmd :=
  .seq (xnmul rD1 rD rD) (.seq (toX (VL.aset L aMuS rD 122)) (toX (VL.aset L aAS rD1 123)))

theorem XV.parkW {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS) (hNN : 48 ≤ L.NN)
    {σ : Env d} {fl k : ℤ} (hz : σ.sc sZ = 0) (hfl : σ.sc sKd = fl) (hk : σ.sc sDmu = k) (bfl : |fl| < 2 ^ ℓ)
    (bk : |k| < 2 ^ ℓ) (hD : σ.nat rD = d) (hdA : d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xparkW L) σ 3 (fun σ' => σ'.sc 125 = fl ∧ σ'.sc sKd = k ∧ σ'.sc 0 = d ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = 0 ∨ y = sKd ∨ y = 125) (fun _ => False) (fun _ _ => False) σ σ') := by
  unfold xparkW
  show XRunsB L X ℓa ℓ _ σ (1 + (1 + 1)) _
  have b0 : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have hz' : σ.sc sZ = ((0 : ℤ) : ℝ) := by rw [hz]; simp
  refine XV.seq (XV.addI hL (x := 125) (a := sKd) (b := sZ) (by omega) (by simp only [sKd]; omega)
    (by simp only [sZ]; omega) hfl hz' bfl b0 (by rwa [add_zero])) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.addI hL (x := sKd) (a := sDmu) (b := sZ) (by simp only [sKd]; omega)
    (by simp only [sDmu]; omega) (by simp only [sZ]; omega) (by rw [sc_setSc_ne _ (by decide)]; exact hk)
    (by rw [sc_setSc_ne _ (by decide)]; exact hz') bk b0 (by rwa [add_zero])) fun σ2 e2 => ?_
  subst e2
  refine XV.mono (XV.ncastI hL (x := 0) (i := rD) (by omega) (by simp only [rD]; omega)
    (by simp only [Env.setSc_nat]; rw [hD]; exact hdA)) le_rfl fun σ3 e3 => ?_
  subst e3
  refine ⟨by simp [sKd], by simp [sKd], by simp [hD], by simp, ?_⟩
  exact (((FrameA.refl _ _ _ σ).setSc (Or.inr (Or.inr rfl)) _).setSc (Or.inr (Or.inl rfl)) _).setSc
    (Or.inl rfl) _

theorem XV.unparkW {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS) {σ : Env d}
    {fl : ℤ} (hfl : σ.sc 125 = fl) (bfl : |fl| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xunparkW L) σ 2 (fun σ' => σ'.sc sZ = 0 ∧ σ'.sc sKd = fl ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = 0 ∨ y = sKd) (fun _ => False) (fun _ _ => False) σ σ') := by
  unfold xunparkW
  show XRunsB L X ℓa ℓ _ σ (1 + 1) _
  have b0 : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  refine XV.seq (XV.sconst hL (x := sZ) (by simp only [sZ]; omega) 0 rfl (by simp)) fun σ1 e1 => ?_
  subst e1
  refine XV.mono (XV.addI hL (x := sKd) (a := 125) (b := sZ) (by simp only [sKd]; omega) (by omega)
    (by simp only [sZ]; omega) (by rw [sc_setSc_ne _ (by decide)]; exact hfl) (u := fl) (v := 0) (by simp) bfl b0
    (by rwa [add_zero])) le_rfl fun σ2 e2 => ?_
  subst e2
  refine ⟨by simp [sKd, sZ], by simp [sKd, sZ], by simp, ?_⟩
  exact ((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setSc (Or.inr rfl) _

theorem XV.cellsW {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS) (hNN : 48 ≤ L.NN)
    (hNA : 16 ≤ L.NA) {σ : Env d} (hD : σ.nat rD = d) (hd : 1 ≤ d) (hb : |σ.sc 122| < 2 ^ ℓ)
    (hy : |σ.sc 123| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xcellsW L) σ 5 (fun σ' => σ'.arr aMuS d = σ.sc 122 ∧ σ'.arr aAS (d * d) = σ.sc 123 ∧
      σ'.draws = σ.draws ∧ FrameA (fun _ => False) (fun j => j = rD1)
        (fun b k => (b = aMuS ∧ k = d) ∨ (b = aAS ∧ k = d * d)) σ σ') := by
  unfold xcellsW
  show XRunsB L X ℓa ℓ _ σ (1 + (2 + 2)) _
  have hA := asz_lt hL (a := 0) (by omega)
  unfold asz at hA
  have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d hd
  refine XV.seq (XV.nmul hL (i := rD1) (a := rD) (b := rD) (by simp only [rD1]; omega) (by simp only [rD]; omega)
    (by simp only [rD]; omega) (by rw [hD]; omega) (by rw [hD]; omega) (by rw [hD]; omega)) fun σ1 e1 => ?_
  subst e1
  have n1 : (σ.setNat rD1 (σ.nat rD * σ.nat rD)).nat rD = d := by rw [nat_setNat_ne _ (by decide)]; exact hD
  have n1' : (σ.setNat rD1 (σ.nat rD * σ.nat rD)).nat rD1 = d * d := by rw [nat_setNat_eq, hD]
  refine XV.seq (XV.aset hL (a := aMuS) (i := rD) (x := 122) (by simp only [aMuS]; omega)
    (by simp only [rD]; omega) (by omega) (by rw [n1]; unfold asz; omega) (by simpa using hb)) fun σ2 e2 => ?_
  subst e2
  refine XV.mono (XV.aset hL (a := aAS) (i := rD1) (x := 123) (by simp only [aAS]; omega)
    (by simp only [rD1]; omega) (by omega) (by simp only [Env.setArr_nat]; rw [n1']; unfold asz; omega)
    (by simpa using hy)) le_rfl fun σ3 e3 => ?_
  subst e3
  refine ⟨?_, ?_, by simp, ?_⟩
  · simp only [Env.setArr_arr, Env.setArr_nat, Env.setArr_sc, n1, n1', Env.setNat_sc]
    simp [aMuS, aAS]
  · simp only [Env.setArr_arr, Env.setArr_nat, Env.setArr_sc, n1, n1', Env.setNat_sc]
    simp
  · have F0 : FrameA (fun _ => False) (fun j => j = rD1)
        (fun b k => (b = aMuS ∧ k = d) ∨ (b = aAS ∧ k = d * d)) σ σ := FrameA.refl _ _ _ σ
    have n1'' : ((σ.setNat rD1 (σ.nat rD * σ.nat rD)).setArr aMuS ((σ.setNat rD1 (σ.nat rD * σ.nat rD)).nat rD)
        ((σ.setNat rD1 (σ.nat rD * σ.nat rD)).sc 122)).nat rD1 = d * d := by
      simp only [Env.setArr_nat]; exact n1'
    exact ((F0.setNat rfl _).setArr (Or.inl ⟨rfl, n1⟩) _).setArr (Or.inr ⟨rfl, n1''⟩) _

/-! ## The two cells keep BL's invariant -/

/-- `ModeRep` reads the slots below `nSP` and the arrays `3, ..., 7`. -/
theorem modeRep_congrW {σ σ' : Env d} {p : ℕ} {mo : Mode d} (h : ModeRep σ p mo)
    (hS : ∀ y < nSP, σ'.sc y = σ.sc y) (hA : ∀ a, 3 ≤ a → a < nAP → ∀ k, σ'.arr a k = σ.arr a k) :
    ModeRep σ' p mo := by
  cases mo with
  | off => simp only [ModeRep] at h ⊢; rw [hS _ (by decide), h]
  | guard => simp only [ModeRep] at h ⊢; rw [hS _ (by decide), h]
  | run st =>
    obtain ⟨h0, h1, ⟨Dm, hDm, hDm', hmu⟩, h3, h4, h5, h6, h7, h8⟩ := h
    refine ⟨by rw [hS _ (by decide), h0], by rw [hS _ (by decide), h1], ⟨Dm, hDm, by rw [hS _ (by decide), hDm'],
      fun j => by rw [hA _ (by decide) (by decide)]; exact hmu j⟩,
      fun i j => by rw [hA _ (by decide) (by decide)]; exact h3 i j,
      fun i j => by rw [hA _ (by decide) (by decide)]; exact h4 i j,
      fun j => by rw [hA _ (by decide) (by decide)]; exact h5 j,
      by rw [hS _ (by decide)]; exact h6, fun j => by rw [hA _ (by decide) (by decide)]; exact h7 j,
      by rw [hS _ (by decide)]; exact h8⟩

/-- **BL's invariant under the two cells**: writing integers at most `2^E` into `aMuS[d]` and `aAS[d·d]` (and scratch
registers) keeps `BLInv`: the position reads `aMuS` below `d` and `aAS` below `d·d`, the state the arrays from `3` on. -/
theorem BLInv.cellsW {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ σ' : Env d}
    (h : BLInv L n m K0 E cfg mo t σ)
    (hF : FrameA (fun _ => False) (fun j => 8 ≤ j) (fun b k => (b = aMuS ∧ k = d) ∨ (b = aAS ∧ k = d * d)) σ σ')
    (h1 : ∃ z : ℤ, σ'.arr aMuS d = z ∧ |z| ≤ 2 ^ E) (h2 : ∃ z : ℤ, σ'.arr aAS (d * d) = z ∧ |z| ≤ 2 ^ E)
    (hd : σ'.draws = σ.draws) : BLInv L n m K0 E cfg mo t σ' := by
  have hN : ∀ j < 8, σ'.nat j = σ.nat j := fun j hj => hF.1 j (by omega)
  have hS : ∀ y, σ'.sc y = σ.sc y := fun y => hF.2.1 y id
  have hA : ∀ b k, ¬ ((b = aMuS ∧ k = d) ∨ (b = aAS ∧ k = d * d)) → σ'.arr b k = σ.arr b k := hF.2.2.1
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := h.regs
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := h.consts
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := h.par
  obtain ⟨DS, hDS, hDS', hmu, hAS⟩ := h.pos
  obtain ⟨Dc, hDc, hDc', hc⟩ := h.ctr
  refine ⟨h.lay, ?_, ?_, ?_, ⟨DS, hDS, by rw [hS, hDS'], fun j => ?_, fun i j => ?_⟩,
    ⟨Dc, hDc, by rw [hA _ _ (by simp only [aC, aMuS, aAS]; omega), hDc'],
      fun j => by rw [hA _ _ (by simp only [aC, aMuS, aAS]; omega)]; exact hc j⟩,
    modeRep_congrW h.mode (fun y _ => hS y) (fun a ha1 _ k => hA a k (by simp only [aMuS, aAS]; omega)),
    by rw [hF.2.2.2.1, h.rounds], by rw [hd, h.draws], ⟨fun y hy => by rw [hS y]; exact h.bnd.1 y hy,
      fun a ha k hk => ?_⟩⟩
  · exact ⟨by rw [hN _ (by decide), r0], by rw [hN _ (by decide), r1], by rw [hN _ (by decide), r2],
      by rw [hN _ (by decide), r3], by rw [hN _ (by decide), r4], by rw [hN _ (by decide), r5],
      by rw [hN _ (by decide), r6], by rw [hN _ (by decide), r7]⟩
  · exact ⟨by rw [hS, c0], by rw [hS, c1], by rw [hS, c2], by rw [hS, c3], by rw [hS, c4], by rw [hS, c5],
      by rw [hS, c6], by rw [hS, c7], by rw [hS, c8]⟩
  · exact ⟨by rw [hS, p0], by rw [hS, p1], by rw [hS, p2], by rw [hS, p3], by rw [hS, p4], by rw [hS, p5],
      by rw [hS, p6], by rw [hS, p7], by rw [hS, p8], by rw [hS, p9], by rw [hS, p10]⟩
  · have := j.2
    rw [hA _ _ (by simp only [aMuS, aAS]; omega)]; exact hmu j
  · have hij : d * (i : ℕ) + j < d * d := by have := i.2; have := j.2; nlinarith
    rw [hA _ _ (by simp only [aMuS, aAS]; omega)]; exact hAS i j
  · by_cases hc' : (a = aMuS ∧ k = d) ∨ (a = aAS ∧ k = d * d)
    · rcases hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h1
      · exact h2
    · rw [hA a k hc']; exact h.bnd.2 a ha k hk

/-! ## The setup up to the cross check -/

/-- **The state after the cross check**: `d` in `rD`, `1` in `rOne`, no row; `0` in `sZ` and the mode slot, `n` in
`sN`, `k'`, `l'` at `0`, `1, 2, 4` in the slots `26, 27, 28`, `k_δ` in `sDmu`, the cross check's flag at `cfgWW` in
`sKd`; the position and the frame centre (integers at most `2^s`); the free cells of the arrays `0, 1, 2` and the arrays
`3, ..., 7` at `0`; the prologue's coins read, no round. -/
structure PreW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : WorldO d) (s : ℕ) (σ : Env d) : Prop where
  nat : σ.nat rD = d ∧ σ.nat rM = 0 ∧ σ.nat rMk = 0 ∧ σ.nat rOne = 1
  sc : σ.sc sZ = 0 ∧ σ.sc sMode = 0 ∧ σ.sc sN = n ∧ σ.sc sK = 0 ∧ σ.sc sL = 0 ∧ σ.sc 26 = 1 ∧ σ.sc 27 = 2 ∧
    σ.sc 28 = 4 ∧ σ.sc sDmu = kDel δ
  flag : σ.sc sKd = ((if crossOK w.orc (cfgWW d n δ r0 R0 a w) then 0 else 1 : ℤ) : ℝ)
  pos : PosIn σ sDS aMuS s ((cfgWW d n δ r0 R0 a w).μS, (cfgWW d n δ r0 R0 a w).AS)
  ctr : PtIn σ aC s a
  arr : (∀ k, d ≤ k → σ.arr aMuS k = 0) ∧ (∀ k, d * d ≤ k → σ.arr aAS k = 0) ∧
    (∀ k, d + 1 ≤ k → σ.arr aC k = 0) ∧ ∀ b, 3 ≤ b → b < nAP → ∀ k, σ.arr b k = 0
  draws : σ.draws = K0O d n δ r0 R0
  rounds : σ.rounds = 0

/-- P0, PARAM at `k_δ`, `sZ := 0`, `k_δ` into `sDmu`, TRI-OGD-O, the coin count, the cross check. -/
def xpreW (xp0 xpar xtri xcoins xcross : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (xp0 L) (.seq (xpar L) (.seq (.base (toX (VL.sconst L sZ 0))) (.seq (.base (xstashW L))
    (.seq (xtri L) (.seq (xcoins L) (xcross L))))))

set_option maxHeartbeats 4000000 in
/-- **The setup up to the cross check** ends in `PreW`, from BL-O's five contracts. -/
theorem preW_run {xp0 xpar xtri xcoins xcross : Layout → XCmdO} {C0 k0 Cp kp Ct kt Cc kc Cx kx nS nN nA : ℕ}
    (h0 : P0SpecO xp0 C0 k0 nS nN nA) (hp : ParamSpecO xpar Cp kp nS nN nA) (ht : TriSpecO xtri Ct kt nS nN nA)
    (hc : CoinsSpecO xcoins Cc kc nS nN nA) (hx : CrossSpecO xcross Cx kx nS nN nA)
    {L : Layout} {w : WorldO d} {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {ℓa ℓ : ℕ}
    (hI : InU d n δ r0 R0) (hL : LayOK L d ℓa) (hR : RoomO L nS nN nA) (hNS : 172 ≤ nS)
    (h0ℓ : C0 * (wU d n δ r0 R0 a + 1) ^ k0 ≤ ℓ) (h0a : C0 * (wU d n δ r0 R0 a + 1) ^ k0 < 2 ^ ℓa)
    (hpℓ : Cp * (wU d n δ r0 R0 a + 1) ^ kp ≤ ℓ) (hpa : Cp * (wU d n δ r0 R0 a + 1) ^ kp < 2 ^ ℓa)
    (htℓ : Ct * (wU d n δ r0 R0 a + 1) ^ kt ≤ ℓ) (hta : Ct * (wU d n δ r0 R0 a + 1) ^ kt < 2 ^ ℓa)
    (hcℓ : Cc * (wU d n δ r0 R0 a + 1) ^ kc ≤ ℓ) (hca : Cc * (wU d n δ r0 R0 a + 1) ^ kc < 2 ^ ℓa)
    (hxℓ : Cx * (wU d n δ r0 R0 a + (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
      Ct * (wU d n δ r0 R0 a + 1) ^ kt)) + 1) ^ kx ≤ ℓ)
    (hxa : Cx * (wU d n δ r0 R0 a + (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
      Ct * (wU d n δ r0 R0 a + 1) ^ kt)) + 1) ^ kx < 2 ^ ℓa)
    (hWℓ : wU d n δ r0 R0 a < ℓ) :
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xpreW xp0 xpar xtri xcoins xcross L) (envSetup rD d)
      (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp + (1 + (1 +
        (Ct * (wU d n δ r0 R0 a + 1) ^ kt + (Cc * (wU d n δ r0 R0 a + 1) ^ kc +
          Cx * (wU d n δ r0 R0 a + (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
            Ct * (wU d n δ r0 R0 a + 1) ^ kt)) + 1) ^ kx))))))
      (PreW n δ r0 R0 a w (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
        Ct * (wU d n δ r0 R0 a + 1) ^ kt))) := by
  obtain ⟨hRS, hRN, hRA⟩ := id hR
  have hd := hI.hd
  unfold xpreW
  -- P0
  refine XVO.seq (h0 d L w n δ r0 R0 a ℓa ℓ hI hL hR h0ℓ h0a) fun σ1 h1 => ?_
  obtain ⟨⟨n1D, n1M, n1Mk, n1One⟩, ⟨c10, c1M, c1N, c1K, c1L, c126, c127, c128, c1Kd⟩, hctr1, ⟨ha1C, ha1⟩, hd1,
    hr1⟩ := h1
  -- PARAM at `k_δ`
  refine XVO.seq (hp d L w n δ r0 R0 a ℓa ℓ σ1 hI hL hR n1D n1One c10 c1M c1N c126 c127 c128 c1Kd hpℓ hpa)
    fun σ2 ⟨hP2, hB2, d2, F2⟩ => ?_
  -- `sZ := 0`
  refine XVO.seq (XVO.ofX (XV.sconst hL (x := sZ) (by suomega) 0 rfl (by simp))) fun σA eA => ?_
  -- `k_δ` into `sDmu`
  have kdA : σA.sc sKd = ((kDel δ : ℤ) : ℝ) := by
    rw [eA, sc_setSc_ne _ (by decide), F2.2.1 sKd (by suomega), c1Kd]; simp
  have zA : σA.sc sZ = ((0 : ℤ) : ℝ) := by rw [eA]; simp
  have b0 : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have bk : |(kDel δ : ℤ)| < 2 ^ ℓ := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast ((kDel_lt_wU a hI).trans hWℓ).trans Nat.lt_two_pow_self
  refine XVO.seq (XVO.ofX (XV.addI hL (x := sDmu) (a := sKd) (b := sZ) (by suomega) (by suomega) (by suomega) kdA
    zA bk b0 (by rwa [add_zero]))) fun σ3 e3 => ?_
  have n3 : ∀ j, j < rP → σ3.nat j = σ1.nat j := fun j hj => by
    rw [e3, Env.setSc_nat, eA, Env.setSc_nat]; exact F2.1 j (by suomega)
  have s3 : ∀ y, y ≠ sZ → y ≠ sDmu → ¬ SPar y → σ3.sc y = σ1.sc y := fun y h h' h'' => by
    rw [e3, sc_setSc_ne _ h', eA, sc_setSc_ne _ h]; exact F2.2.1 y h''
  have a3 : ∀ b k, b < 8 → σ3.arr b k = σ1.arr b k := fun b k hb => by
    rw [e3, Env.setSc_arr, eA, Env.setSc_arr]; exact F2.2.2.1 b k (by suomega)
  have z3 : σ3.sc sZ = 0 := by rw [e3, sc_setSc_ne _ (by decide), zA]; simp
  have dm3 : σ3.sc sDmu = kDel δ := by rw [e3]; simp
  have P3 : ParO σ3 (parO d n δ) :=
    hP2.congr (fun j _ _ => by rw [e3, Env.setSc_nat, eA, Env.setSc_nat]) fun y h1 h2 => by
      rw [e3, sc_setSc_ne _ (by suomega), eA, sc_setSc_ne _ (by suomega)]
  have B3 : SlotBnd σ3 4 22 (Cp * (wU d n δ r0 R0 a + 1) ^ kp) :=
    hB2.congr fun y h1 h2 => by rw [e3, sc_setSc_ne _ (by suomega), eA, sc_setSc_ne _ (by suomega)]
  have bas3 : BasO n σ3 :=
    ⟨(n3 rD (by decide)).trans n1D, (n3 rOne (by decide)).trans n1One, z3,
      (s3 sN (by decide) (by decide) (by suomega)).trans c1N,
      (s3 26 (by decide) (by decide) (by suomega)).trans c126,
      (s3 27 (by decide) (by decide) (by suomega)).trans c127,
      (s3 28 (by decide) (by decide) (by suomega)).trans c128⟩
  have kd3 : σ3.sc sKd = kDel δ := (s3 sKd (by decide) (by decide) (by suomega)).trans c1Kd
  have dr3 : σ3.draws = 0 := by rw [e3, Env.setSc_draws, eA, Env.setSc_draws, d2, hd1]
  have rd3 : σ3.rounds = 0 := by rw [e3, Env.setSc_rounds, eA, Env.setSc_rounds, F2.2.2.2.1, hr1]
  -- TRI-OGD-O
  refine XVO.seq (ht d L w n δ r0 R0 a ℓa ℓ σ3 hI hL hR bas3 kd3 htℓ hta) fun σ4 ⟨hPos4, hLp4, d4, F4⟩ => ?_
  have eS : (posO d n w.orc δ r0 R0 a fun j => w.cs (σ3.draws + j)) =
      ((cfgWW d n δ r0 R0 a w).μS, (cfgWW d n δ r0 R0 a w).AS) := by
    rw [show (fun j => w.cs (σ3.draws + j)) = w.cs from funext fun j => by rw [dr3, zero_add]]
    rfl
  rw [eS] at hPos4
  have bas4 : BasO n σ4 := bas3.congr (fun j hj => F4.1 j (by suomega)) fun y hy => F4.2.1 y (by suomega)
  have P4 : ParO σ4 (parO d n δ) := P3.frame F4 (fun y h1 h2 => by suomega) fun j h1 h2 => by suomega
  -- the coin count
  refine XVO.seq (hc d L w n δ r0 R0 a ℓa ℓ σ4 hI hL hR bas4 P4 hLp4 hcℓ hca) fun σ5 ⟨d5, F5⟩ => ?_
  have bas5 : BasO n σ5 := bas4.congr (fun j hj => F5.1 j (by suomega)) fun y hy => F5.2.1 y (by suomega)
  have P5 : ParO σ5 (parO d n δ) := P4.frame F5 (fun y h1 h2 => by suomega) fun j h1 h2 => by suomega
  have B5 : SlotBnd σ5 4 22 (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
      Ct * (wU d n δ r0 R0 a + 1) ^ kt)) :=
    (B3.congr fun y h1 h2 => (F5.2.1 y (by suomega)).trans (F4.2.1 y (by suomega))).mono (by omega)
  have Pos5 : PosIn σ5 sDS aMuS (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
      Ct * (wU d n δ r0 R0 a + 1) ^ kt)) ((cfgWW d n δ r0 R0 a w).μS, (cfgWW d n δ r0 R0 a w).AS) :=
    (posIn_congr hPos4 (F5.2.1 _ (by suomega)) (fun k => F5.2.2.1 _ k (by suomega))
      fun k => F5.2.2.1 _ k (by suomega)) |> (posIn_mono · (by omega))
  have Ctr5 : PtIn σ5 aC (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
      Ct * (wU d n δ r0 R0 a + 1) ^ kt)) a :=
    ptIn_mono (ptIn_congr hctr1 fun k => by
      rw [F5.2.2.1 aC k (by suomega), F4.2.2.1 aC k (by suomega), a3 aC k (by decide)]) (by omega)
  -- the cross check
  refine XVO.mono (hx d L w n δ r0 R0 a ℓa ℓ _ _ σ5 hI hL hR bas5 P5 B5 Pos5 Ctr5 hxℓ hxa) le_rfl
    fun σ6 ⟨hfl6, d6, F6⟩ => ?_
  have nat61 : ∀ j, j < 4 → σ6.nat j = σ1.nat j := fun j hj => by
    rw [F6.1 j (by suomega), F5.1 j (by suomega), F4.1 j (by suomega), n3 j (by suomega)]
  have sc63 : ∀ y, y < 29 → y ≠ 22 → σ6.sc y = σ3.sc y := fun y h1 h2 => by
    rw [F6.2.1 y (by suomega), F5.2.1 y (by suomega), F4.2.1 y (by suomega)]
  have sc61 : ∀ y, y < 29 → y ≠ sDS → y ≠ sZ → y ≠ sDmu → ¬ SPar y → σ6.sc y = σ1.sc y :=
    fun y h1 h2 h3 h4 h5 => (sc63 y h1 h2).trans (s3 y h3 h4 h5)
  have arr61 : ∀ b k, b < 8 → ¬ ATri d b k → σ6.arr b k = σ1.arr b k := fun b k h1 h2 => by
    rw [F6.2.2.1 b k (by suomega), F5.2.2.1 b k (by suomega), F4.2.2.1 b k h2, a3 b k h1]
  refine ⟨⟨(nat61 rD (by decide)).trans n1D, (nat61 rM (by decide)).trans n1M, (nat61 rMk (by decide)).trans n1Mk,
      (nat61 rOne (by decide)).trans n1One⟩,
    ⟨(sc63 sZ (by decide) (by decide)).trans z3,
      (sc61 sMode (by decide) (by decide) (by decide) (by decide) (by suomega)).trans c1M,
      (sc61 sN (by decide) (by decide) (by decide) (by decide) (by suomega)).trans c1N,
      (sc61 sK (by decide) (by decide) (by decide) (by decide) (by suomega)).trans c1K,
      (sc61 sL (by decide) (by decide) (by decide) (by decide) (by suomega)).trans c1L,
      (sc61 26 (by decide) (by decide) (by decide) (by decide) (by suomega)).trans c126,
      (sc61 27 (by decide) (by decide) (by decide) (by decide) (by suomega)).trans c127,
      (sc61 28 (by decide) (by decide) (by decide) (by decide) (by suomega)).trans c128,
      (sc63 sDmu (by decide) (by decide)).trans dm3⟩,
    hfl6.trans (congrArg (fun z : ℤ => (z : ℝ)) (if_congr (crossOK_cfgS_cfgWW d n δ r0 R0 a w) rfl rfl)),
    posIn_congr Pos5 (F6.2.1 _ (by suomega)) (fun k => F6.2.2.1 _ k (by suomega))
      (fun k => F6.2.2.1 _ k (by suomega)),
    ptIn_congr Ctr5 (fun k => F6.2.2.1 _ k (by suomega)),
    ⟨fun k hk => (arr61 aMuS k (by decide) (by suomega)).trans (ha1 aMuS (by decide) (by decide) k),
      fun k hk => (arr61 aAS k (by decide) (by suomega)).trans (ha1 aAS (by decide) (by decide) k),
      fun k hk => (arr61 aC k (by decide) (by suomega)).trans (ha1C k hk),
      fun b hb1 hb2 k => by
        simp only [nAP] at hb2
        exact (arr61 b k (by omega) (by suomega)).trans (ha1 b (by suomega) (by suomega) k)⟩,
    ?_, ?_⟩
  · have := LposO_le_K0O d n δ r0 R0
    rw [d6, d5, d4, dr3]
    omega
  · rw [F6.2.2.2.1, F5.2.2.2.1, F4.2.2.2.1, rd3]

/-! ## The setup from PARAM-W on -/

/-- The flag and `k_δ` moved, PARAM-W, the flag back, the epoch start, the mode, the two cells. -/
def xpostW (xpw xmode : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (.base (xparkW L)) (.seq (xpw L) (.seq (.base (xunparkW L)) (.seq (.base (xepoch L)) (.seq (xmode L)
    (.base (xcellsW L))))))

set_option maxHeartbeats 4000000 in
/-- **The setup from PARAM-W on** ends in BL-OW's invariant at round `0` and the two cells, from `PreW`. -/
theorem postW_run {xpw xmode : Layout → XCmdO} {Cw kw Cm nS nN nA : ℕ} (hw : ParamWSpecS xpw Cw kw nS nN nA)
    (hm : ModeSpecO xmode Cm nS nN nA) {L : Layout} {w : WorldO d} {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
    {E ℓa ℓ s : ℕ} {σ : Env d} (hI : InU d n δ r0 R0) (hL : LayOK L d ℓa) (hR : RoomO L nS nN nA)
    (hNS : 172 ≤ nS) (hNN : 48 ≤ nN) (hNA : 16 ≤ nA)
    (hwℓ : Cw * (wU d n δ r0 R0 a + 1) ^ kw + 2 ≤ ℓ) (hwa : Cw * (wU d n δ r0 R0 a + 1) ^ kw < 2 ^ ℓa)
    (hsE : s + Cw * (wU d n δ r0 R0 a + 1) ^ kw ≤ E) (hE1 : 1 ≤ E) (hnE : (n : ℤ) ≤ 2 ^ E)
    (hWℓ : wU d n δ r0 R0 a < ℓ) (hpre : PreW n δ r0 R0 a w s σ) :
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xpostW xpw xmode L) σ
      (3 + (Cw * (wU d n δ r0 R0 a + 1) ^ kw + (2 + (epochUnits d + (Cm + 5)))))
      (fun σ' => BLOInv L n (K0O d n δ r0 R0) E (cfgWW d n δ r0 R0 a w) (modeOW d n δ r0 R0 a w 0) 0 σ' ∧
        CellsW σ' n δ) := by
  obtain ⟨hRS, hRN, hRA⟩ := id hR
  have hd := hI.hd
  obtain ⟨⟨n0D, n0M, n0Mk, n0One⟩, ⟨c0Z, c0M, c0N, c0K, c0L, c026, c027, c028, c0Dm⟩, hfl0, hpos0, hctr0,
    ⟨ha0mu, ha0AS, ha0C, ha0⟩, hd0, hr0⟩ := hpre
  have hℓ2 : 2 < ℓ := by have := hWℓ; unfold wU at this; omega
  have h1ℓ : (1 : ℤ) < 2 ^ ℓ := one_lt_pow₀ (by norm_num) (by omega)
  have bfl : |(if crossOK w.orc (cfgWW d n δ r0 R0 a w) then 0 else 1 : ℤ)| < 2 ^ ℓ := by
    split_ifs <;> simp only [abs_zero, abs_one] <;> linarith
  have bk : |(kDel δ : ℤ)| < 2 ^ ℓ := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast ((kDel_lt_wU a hI).trans hWℓ).trans Nat.lt_two_pow_self
  have hdA : d < 2 ^ ℓa := by
    have := asz_lt hL (a := 0) (by omega)
    unfold asz at this
    omega
  unfold xpostW
  -- the flag and `k_δ` moved, `d` into the slot `0`
  refine XVO.seq (XVO.ofX (XV.parkW hL (by omega) (by omega) c0Z hfl0 (by rw [c0Dm]; simp) bfl bk n0D hdA))
    fun σ1 ⟨e1fl, e1k, e10, d1, F1⟩ => ?_
  have sc10 : ∀ y, y ≠ 0 → y ≠ sKd → y ≠ 125 → σ1.sc y = σ.sc y := fun y h1 h2 h3 =>
    F1.2.1 y (by simp only [sKd] at h2 ⊢; omega)
  -- PARAM-W
  refine XVO.seq (hw d L w n δ r0 R0 a ℓa ℓ σ1 hI hL hR (by rw [F1.1 rD id]; exact n0D)
    (by rw [F1.1 rOne id]; exact n0One) e10 (by rw [sc10 sMode (by decide) (by decide) (by decide)]; exact c0M)
    (by rw [sc10 sN (by decide) (by decide) (by decide)]; exact c0N)
    (by rw [sc10 26 (by decide) (by decide) (by decide)]; exact c026)
    (by rw [sc10 27 (by decide) (by decide) (by decide)]; exact c027)
    (by rw [sc10 28 (by decide) (by decide) (by decide)]; exact c028) (by rw [e1k]; simp) (by omega) hwa)
    fun σ2 ⟨P2, B2, hb2, hy2, bb2, by2, d2, F2⟩ => ?_
  -- the flag back, `0` into the slot `0`
  have fl2 : σ2.sc 125 = (((if crossOK w.orc (cfgWW d n δ r0 R0 a w) then 0 else 1 : ℤ)) : ℝ) := by
    rw [F2.2.1 125 (by suomega), e1fl]
  refine XVO.seq (XVO.ofX (XV.unparkW hL (by omega) fl2 bfl)) fun σ3 ⟨e3Z, e3k, d3, F3⟩ => ?_
  -- the epoch start
  obtain ⟨zA, hzA, bA⟩ := B2 sA0 (by decide) (by decide)
  obtain ⟨zB, hzB, bB⟩ := B2 sB0 (by decide) (by decide)
  have eA : zA = qn (parOW d n δ).p (parOW d n δ).A0 := int_of_sc hzA P2.par.2.2.2.2.2.2.2.2.2.1
  have eB : zB = qn (parOW d n δ).p (parOW d n δ).B0 := int_of_sc hzB P2.par.2.2.2.2.2.2.2.2.2.2
  subst eA eB
  have nat32 : ∀ j, j < rP → σ3.nat j = σ.nat j := fun j hj => by
    rw [F3.1 j id, F2.1 j (by suomega), F1.1 j id]
  have hA3 : σ3.sc sA0 = ((qn (parOW d n δ).p (parOW d n δ).A0 : ℤ) : ℝ) :=
    (F3.2.1 sA0 (by suomega)).trans hzA
  have hB3 : σ3.sc sB0 = ((qn (parOW d n δ).p (parOW d n δ).B0 : ℤ) : ℝ) :=
    (F3.2.1 sB0 (by suomega)).trans hzB
  refine XVO.seq (XVO.ofX (XV.epoch (E := Cw * (wU d n δ r0 R0 a + 1) ^ kw) hL (by omega) (by omega) (by omega)
    ((nat32 rD (by decide)).trans n0D) ((nat32 rOne (by decide)).trans n0One) e3Z hA3 hB3 bA bB (by omega)))
    fun σ4 ⟨hF4, hDm4, hA4, hB4, d4, F4⟩ => ?_
  -- the mode
  have P4 : ParO σ4 (parOW d n δ) :=
    (P2.frame F3 (fun y _ _ => by suomega) fun j _ _ => id).frame F4 (fun y _ _ => by suomega)
      fun j _ _ => by suomega
  have B4 : SlotBnd σ4 4 22 (Cw * (wU d n δ r0 R0 a + 1) ^ kw) :=
    B2.congr fun y h1 h2 => (F4.2.1 y (by suomega)).trans (F3.2.1 y (by suomega))
  obtain ⟨zP, hzP, bP⟩ := B4 s2pF (by decide) (by decide)
  obtain ⟨zE, hzE, bE⟩ := B4 sEps (by decide) (by decide)
  have ePF : zP = 2 ^ (parOW d n δ).pF := int_of_sc hzP (by rw [P4.consts.2.1]; push_cast; rfl)
  have eEp : zE = qn (parOW d n δ).pF (parOW d n δ).eps := int_of_sc hzE P4.par.1
  subst ePF eEp
  have hz4 : σ4.sc sZ = 0 := (F4.2.1 sZ (by suomega)).trans e3Z
  have hfl4 : σ4.sc sBadS = (((if crossOK w.orc (cfgWW d n δ r0 R0 a w) then 0 else 1 : ℤ)) : ℝ) :=
    (F4.2.1 sBadS (by suomega)).trans e3k
  have hm4 : σ4.sc sMode = 0 := by
    rw [F4.2.1 sMode (by suomega), F3.2.1 sMode (by suomega), F2.2.1 sMode (by suomega),
      sc10 sMode (by decide) (by decide) (by decide)]
    exact c0M
  have b2 : (2 : ℤ) ^ (Cw * (wU d n δ r0 R0 a + 1) ^ kw + 2) ≤ 2 ^ ℓ :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have bsp : (0 : ℤ) < 2 ^ (Cw * (wU d n δ r0 R0 a + 1) ^ kw) := by positivity
  have e4 : (2 : ℤ) ^ (Cw * (wU d n δ r0 R0 a + 1) ^ kw + 2) = 4 * 2 ^ (Cw * (wU d n δ r0 R0 a + 1) ^ kw) := by
    ring
  refine XVO.seq (hm d L _ ℓa ℓ σ4 _ _ _ hL hR hz4 hfl4 hzP hzE hm4 bfl (by linarith)
    (by rw [abs_mul, abs_two]; linarith) (by omega)) fun σ5 ⟨hm5, d5, F5⟩ => ?_
  -- BL-OW's invariant at round `0`
  have nat50 : ∀ j, j < 4 → σ5.nat j = σ.nat j := fun j hj => by
    rw [F5.1 j id, F4.1 j (by suomega), nat32 j (by suomega)]
  have sc50 : ∀ y, y < 30 → y ≠ 0 → y ≠ 1 → y ≠ 2 → y ≠ 23 → y ≠ 29 → ¬ SPar y → σ5.sc y = σ.sc y :=
    fun y h1 h2 h3 h4 h5 h6 h7 => by
      rw [F5.2.1 y (by suomega), F4.2.1 y (by suomega), F3.2.1 y (by suomega), F2.2.1 y h7,
        sc10 y h2 (by simp only [sKd]; omega) (by omega)]
  have arr50 : ∀ b k, b < 8 → b ≠ aA → b ≠ aB → σ5.arr b k = σ.arr b k := fun b k h1 h2 h3 => by
    rw [F5.2.2.1 b k id, F4.2.2.1 b k (fun h => h.1.elim h2 h3), F3.2.2.1 b k id, F2.2.2.1 b k (by suomega),
      F1.2.2.1 b k id]
  have inv5 : BLOInv L n (K0O d n δ r0 R0) E (cfgWW d n δ r0 R0 a w) (modeOW d n δ r0 R0 a w 0) 0 σ5 :=
    bloInv_mk (s := s + Cw * (wU d n δ r0 R0 a + 1) ^ kw) (orc := w.orc) (c := cfgWW d n δ r0 R0 a w)
      ⟨by simp only [nN0]; omega, by simp only [nS0]; omega, by simp only [nA0]; omega⟩ hsE hE1 hnE
      (parOW_half_iff d n δ) (parOW_onG_A0 d n δ) (parOW_onG_B0 d n δ)
      ((nat50 rD (by decide)).trans n0D) ((nat50 rM (by decide)).trans n0M) ((nat50 rMk (by decide)).trans n0Mk)
      ((nat50 rOne (by decide)).trans n0One) (P4.frame F5 (fun y _ _ => by suomega) fun j _ _ => id)
      ((B4.congr fun y _ _ => F5.2.1 y (by suomega)).mono (by omega))
      ((F5.2.1 sZ (by suomega)).trans hz4)
      ((sc50 sN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by suomega)).trans c0N)
      ((F5.2.1 sFirst (by suomega)).trans hF4) ((F5.2.1 sDmu (by suomega)).trans hDm4)
      ((sc50 sK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by suomega)).trans c0K)
      ((sc50 sL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by suomega)).trans c0L)
      hm5
      (posIn_mono (posIn_congr hpos0
        (sc50 sDS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by suomega))
        (fun k => arr50 _ k (by decide) (by decide) (by decide))
        fun k => arr50 _ k (by decide) (by decide) (by decide)) (by omega))
      (fun k hk => (arr50 aMuS k (by decide) (by decide) (by decide)).trans (ha0mu k hk))
      (fun k hk => (arr50 aAS k (by decide) (by decide) (by decide)).trans (ha0AS k hk))
      (ptIn_mono (ptIn_congr hctr0 fun k => arr50 aC k (by decide) (by decide) (by decide)) (by omega))
      (fun k hk => (arr50 aC k (by decide) (by decide) (by decide)).trans (ha0C k hk))
      (fun k => (arr50 aMu k (by decide) (by decide) (by decide)).trans (ha0 aMu (by decide) (by decide) k))
      (fun k => (arr50 ab k (by decide) (by decide) (by decide)).trans (ha0 ab (by decide) (by decide) k))
      (fun k => (arr50 aG k (by decide) (by decide) (by decide)).trans (ha0 aG (by decide) (by decide) k))
      (fun k => by
        rw [F5.2.2.1 aA k id]
        split_ifs with h
        · obtain ⟨j, hj, rfl⟩ := h; exact hA4 j hj
        · rw [F4.2.2.1 aA k (fun h' => h h'.2), F3.2.2.1 aA k id, F2.2.2.1 aA k (by suomega), F1.2.2.1 aA k id]
          exact ha0 aA (by decide) (by decide) k)
      (fun k => by
        rw [F5.2.2.1 aB k id]
        split_ifs with h
        · obtain ⟨j, hj, rfl⟩ := h; exact hB4 j hj
        · rw [F4.2.2.1 aB k (fun h' => h h'.2), F3.2.2.1 aB k id, F2.2.2.1 aB k (by suomega), F1.2.2.1 aB k id]
          exact ha0 aB (by decide) (by decide) k)
      (by rw [F5.2.2.2.1, F4.2.2.2.1, F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1, hr0])
      (by rw [d5, d4, d3, d2, d1, hd0])
  -- the two cells
  have hb5 : σ5.sc 122 = ((qn (parO d n δ).p (b0OW d n δ) : ℤ) : ℝ) := by
    rw [F5.2.1 122 (by suomega), F4.2.1 122 (by suomega), F3.2.1 122 (by suomega)]; exact hb2
  have hy5 : σ5.sc 123 = ((qn (parO d n δ).p (y0OW d n δ) : ℤ) : ℝ) := by
    rw [F5.2.1 123 (by suomega), F4.2.1 123 (by suomega), F3.2.1 123 (by suomega)]; exact hy2
  have hwlt : (2 : ℤ) ^ (Cw * (wU d n δ r0 R0 a + 1) ^ kw) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hwE : (2 : ℤ) ^ (Cw * (wU d n δ r0 R0 a + 1) ^ kw) ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) (by omega)
  refine XVO.mono (XVO.ofX (XV.cellsW hL (by omega) (by omega) (by omega) ((nat50 rD (by decide)).trans n0D) hd
    (by rw [hb5]; exact XV.abs_int_lt (bb2.trans_lt hwlt)) (by rw [hy5]; exact XV.abs_int_lt (by2.trans_lt hwlt)))) (by omega)
    fun σ6 ⟨h6b, h6y, d6, F6⟩ => ⟨BLInv.cellsW inv5 (F6.mono (fun _ h => h) (fun j h => by subst h; decide)
      (fun _ _ h => h)) ⟨_, h6b.trans hb5, bb2.trans hwE⟩ ⟨_, h6y.trans hy5, by2.trans hwE⟩ d6,
      h6b.trans hb5, h6y.trans hy5⟩

/-! ## The assembly -/

/-- **BL-OW's setup**: BL-O's setup up to the cross check, then PARAM-W, the epoch start, the mode and the two cells. -/
def xinitW (xp0 xpar xtri xcoins xcross xpw xmode : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (xpreW xp0 xpar xtri xcoins xcross L) (xpostW xpw xmode L)

set_option maxHeartbeats 2000000 in
/-- **The setup contract of BL-OW from the sub-block contracts**: BL-O's six (P0, PARAM at `k_δ`, TRI-OGD-O, the coin
count, the cross check, the mode) and PARAM-W's give `SetupSpecW` for `xinitW` at BL-O's constants `csO`, `ksO`, with
PARAM-W's constants added to PARAM's and `11` units for the new moves. -/
theorem setupSpecW_of {xp0 xpar xtri xcoins xcross xpw xmode : Layout → XCmdO}
    {C0 k0 Cp kp Ct kt Cc kc Cx kx Cw kw Cm nS nN nA : ℕ}
    (h0 : P0SpecO xp0 C0 k0 nS nN nA) (hp : ParamSpecO xpar Cp kp nS nN nA) (ht : TriSpecO xtri Ct kt nS nN nA)
    (hc : CoinsSpecO xcoins Cc kc nS nN nA) (hx : CrossSpecO xcross Cx kx nS nN nA)
    (hw : ParamWSpecS xpw Cw kw nS nN nA) (hm : ModeSpecO xmode Cm nS nN nA) (hNS : 172 ≤ nS) (hNN : 48 ≤ nN)
    (hNA : 16 ≤ nA) :
    SetupSpecW (xinitW xp0 xpar xtri xcoins xcross xpw xmode) (csO C0 (Cp + Cw) Ct Cc Cx kx (Cm + 11))
      (ksO k0 (kp + kw) kt kc kx) nS nN nA := by
  intro d L w n δ r0 R0 a E ℓa ℓ hI hL hR hE hℓ hℓa
  have hd := hI.hd
  have hep : epochUnits d ≤ 25 * (wU d n δ r0 R0 a + 1) := by unfold epochUnits wU; omega
  obtain ⟨b0, bp, bt, bc, bx, bs, bW, bK⟩ :=
    setupO_bounds (wU d n δ r0 R0 a) C0 k0 (Cp + Cw) (kp + kw) Ct kt Cc kc Cx kx (Cm + 11) (epochUnits d) hep
  have hpw : Cp * (wU d n δ r0 R0 a + 1) ^ kp + Cw * (wU d n δ r0 R0 a + 1) ^ kw ≤
      (Cp + Cw) * (wU d n δ r0 R0 a + 1) ^ (kp + kw) := by
    have h1 : (wU d n δ r0 R0 a + 1) ^ kp ≤ (wU d n δ r0 R0 a + 1) ^ (kp + kw) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (wU d n δ r0 R0 a + 1) ^ kw ≤ (wU d n δ r0 R0 a + 1) ^ (kp + kw) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
  have hxW : Cx * (wU d n δ r0 R0 a + (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
      Ct * (wU d n δ r0 R0 a + 1) ^ kt)) + 1) ^ kx ≤
      Cx * (wU d n δ r0 R0 a + (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + ((Cp + Cw) * (wU d n δ r0 R0 a + 1) ^ (kp + kw) +
        Ct * (wU d n δ r0 R0 a + 1) ^ kt)) + 1) ^ kx :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hYE : (wU d n δ r0 R0 a + 1) ^ ksO k0 (kp + kw) kt kc kx ≤
      (wU d n δ r0 R0 a + E + 1) ^ ksO k0 (kp + kw) kt kc kx := Nat.pow_le_pow_left (by omega) _
  have hYE' := Nat.mul_le_mul_left (csO C0 (Cp + Cw) Ct Cc Cx kx (Cm + 11)) hYE
  have hns : n.size ≤ wU d n δ r0 R0 a := by unfold wU; omega
  have hnE : (n : ℤ) ≤ 2 ^ E := by
    have h1 : n < 2 ^ n.size := Nat.lt_size_self n
    have h2 : 2 ^ n.size ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast (h1.trans_le h2).le
  unfold xinitW
  refine XVO.mono (XVO.seq (preW_run h0 hp ht hc hx hI hL hR hNS (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun σ hσ =>
      XVO.mono (postW_run hw hm hI hL hR hNS hNN hNA (E := E) (by omega) (by omega) (by omega) (by omega) hnE
        (by omega) hσ) le_rfl fun σ' h' => ⟨h', posBnd_of_posInO (posIn_mono hσ.pos (by omega))⟩) (by omega)
    fun _ h => h

/-! ## `ProgSetupW` -/

/-- **`ProgSetupW` from the seven sub-block contracts**, each for some command, constants and room. -/
theorem progSetupW_of (h0 : ∃ (xp0 : Layout → XCmdO) (C k nS nN nA : ℕ), P0SpecO xp0 C k nS nN nA)
    (hp : ∃ (xpar : Layout → XCmdO) (C k nS nN nA : ℕ), ParamSpecO xpar C k nS nN nA)
    (ht : ∃ (xtri : Layout → XCmdO) (C k nS nN nA : ℕ), TriSpecO xtri C k nS nN nA)
    (hc : ∃ (xcoins : Layout → XCmdO) (C k nS nN nA : ℕ), CoinsSpecO xcoins C k nS nN nA)
    (hx : ∃ (xcross : Layout → XCmdO) (C k nS nN nA : ℕ), CrossSpecO xcross C k nS nN nA)
    (hw : ∃ (xpw : Layout → XCmdO) (C k nS nN nA : ℕ), ParamWSpecS xpw C k nS nN nA)
    (hm : ∃ (xmode : Layout → XCmdO) (C nS nN nA : ℕ), ModeSpecO xmode C nS nN nA) : ProgSetupW := by
  obtain ⟨x0, C0, k0, s0, n0, a0, h0⟩ := h0
  obtain ⟨xp, Cp, kp, sp, np, ap, hp⟩ := hp
  obtain ⟨xt, Ct, kt, st, nt, at', ht⟩ := ht
  obtain ⟨xc, Cc, kc, sc, nc, ac, hc⟩ := hc
  obtain ⟨xx, Cx, kx, sx, nx, ax, hx⟩ := hx
  obtain ⟨xw, Cw, kw, sw, nw, aw, hw⟩ := hw
  obtain ⟨xm, Cm, sm, nm, am, hm⟩ := hm
  refine ⟨_, _, _, s0 + sp + st + sc + sx + sw + sm + 172, n0 + np + nt + nc + nx + nw + nm + 48,
    a0 + ap + at' + ac + ax + aw + am + 16, setupSpecW_of (xp0 := x0) (xpar := xp) (xtri := xt) (xcoins := xc)
      (xcross := xx) (xpw := xw) (xmode := xm) (h0.room (by omega) (by omega) (by omega))
      (hp.room (by omega) (by omega) (by omega)) (ht.room (by omega) (by omega) (by omega))
      (hc.room (by omega) (by omega) (by omega)) (hx.room (by omega) (by omega) (by omega))
      (hw.room (by omega) (by omega) (by omega)) (hm.room (by omega) (by omega) (by omega)) (by omega) (by omega)
      (by omega)⟩

/-- **BL-OW's setup on the oracle bit RAM** from PARAM-W's contract, with BL-O's six proved setup contracts. -/
theorem progSetupW (hw : ∃ (xpw : Layout → XCmdO) (C k nS nN nA : ℕ), ParamWSpecS xpw C k nS nN nA) :
    ProgSetupW :=
  progSetupW_of ⟨_, _, _, _, _, _, p0SpecO⟩ ⟨_, _, _, _, _, _, paramSpecO⟩ ⟨_, _, _, _, _, _, TriO.triSpecO_prog⟩
    ⟨_, _, _, _, _, _, coinsSpecO⟩ ⟨_, _, _, _, _, _, crossSpecO⟩ hw ⟨_, _, _, _, _, modeSpecO⟩

end AdversarialBco.UW.ProgW
