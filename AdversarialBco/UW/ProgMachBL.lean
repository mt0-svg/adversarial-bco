/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOBL
public import AdversarialBco.UW.ProgPure

@[expose] public section

/-!
# BL-OW's program on the oracle machine: the invariant, the two contracts and the assembly

The BL-OW instance of Unified/ProgOBL.lean (copied: the setup contract `SetupSpecO`, the round contract and the
assembly; reused: the driver `progO`, `progBLO`, `DrvKO`, `drvO_poly`, `frozenO_form`, `costOKO_mono`, `spaceOKO_mono`).
BL-OW's program is `progBLO xinit xA xM xB L` with BL-OW's setup and round; its run is `trajOW` (UW/ProgPure.lean) on
the configuration `cfgWW`.

* `CellsW`: the two cells that carry PARAM-W's thresholds across the rounds, `2^p b0` in `aMuS[d]` and `2^p y0` in
  `aAS[d·d]` (free entries of the position's arrays, which no block writes after the setup);
* `SetupSpecW`, `RoundSpecW`: the setup and round contracts of BL-O with BL-OW's configuration, modes and plays, and
  the cells in the invariant;
* `progBLOW_world`, `bloWLink_of`, `bloWMachOK_of`, `theoremProgW_of`: the assembly, as for BL-O.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.Unified (initU CoinWindowsOK)
open AdversarialBco.UW.BLOW (cfgWW modeOW playOW readOW b0OW y0OW parOW)
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO

variable {d : ℕ}

/-! ## The cells of the thresholds and the contracts -/

/-- **The cells of PARAM-W's thresholds**: `qn p b0` in `aMuS[d]`, `qn p y0` in `aAS[d·d]`, at BL-O's precision `p`. -/
def CellsW (σ : Env d) (n : ℕ) (δ : ℚ) : Prop :=
  σ.arr aMuS d = ((qn (parO d n δ).p (b0OW d n δ) : ℤ) : ℝ) ∧
    σ.arr aAS (d * d) = ((qn (parO d n δ).p (y0OW d n δ) : ℤ) : ℝ)

/-- The cells pass through any change that keeps the arrays `aMuS`, `aAS`. -/
theorem CellsW.congr {σ σ' : Env d} {n : ℕ} {δ : ℚ} (h : CellsW σ n δ) (h0 : σ'.arr aMuS d = σ.arr aMuS d)
    (h1 : σ'.arr aAS (d * d) = σ.arr aAS (d * d)) : CellsW σ' n δ :=
  ⟨h0.trans h.1, h1.trans h.2⟩

/-- **The setup contract of BL-OW.** `SetupSpecO` with BL-OW's configuration and first mode, and the cells. -/
def SetupSpecW (xinit : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (E ℓa ℓ : ℕ),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA → C * (wU d n δ r0 R0 a + 1) ^ k ≤ E →
    C * (wU d n δ r0 R0 a + E + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + E + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xinit L) (envSetup rD d) (C * (wU d n δ r0 R0 a + E + 1) ^ k)
      (fun σ => (BLOInv L n (K0O d n δ r0 R0) E (cfgWW d n δ r0 R0 a w) (modeOW d n δ r0 R0 a w 0) 0 σ ∧
        CellsW σ n δ) ∧ PosBnd (cfgV (cfgWW d n δ r0 R0 a w)) (C * (wU d n δ r0 R0 a + 1) ^ k))

/-- **The round contract of BL-OW**, in three segments: the round contract of BL-O with BL-OW's configuration, modes and
plays, and the cells kept. -/
def RoundSpecW (xA xM xB : Layout → XCmdO) (C k Cn kn nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (E0 E ℓa ℓ t : ℕ) (σ : Env d),
    InU d n δ r0 R0 → t < n → LayOK L d ℓa → RoomO L nS nN nA →
    PosBnd (cfgV (cfgWW d n δ r0 R0 a w)) E0 → Cn * (wU d n δ r0 R0 a + E0 + 1) ^ kn ≤ E →
    C * (wU d n δ r0 R0 a + E + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + E + 1) ^ k < 2 ^ ℓa →
    BLOInv L n (K0O d n δ r0 R0) E (cfgWW d n δ r0 R0 a w) (modeOW d n δ r0 R0 a w t) t σ → CellsW σ n δ →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xA L) σ (C * (wU d n δ r0 R0 a + E + 1) ^ k) (fun σA =>
      σA.rounds = t ∧ σA.draws = DO' d n δ r0 R0 a t ∧
      XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xM L) σA (C * (wU d n δ r0 R0 a + E + 1) ^ k) (fun σM =>
        σM.rounds = t + 1 ∧ σM.draws = DO' d n δ r0 R0 a t ∧ σM.pts t = toE (playOW d n δ r0 R0 a w t) ∧
        XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xB L) σM (C * (wU d n δ r0 R0 a + E + 1) ^ k)
          (fun σ' => BLOInv L n (K0O d n δ r0 R0) E (cfgWW d n δ r0 R0 a w) (modeOW d n δ r0 R0 a w (t + 1))
            (t + 1) σ' ∧ CellsW σ' n δ)))

/-! ## The assembly on one input and one world -/

/-- The cost, space and coin clauses and the plays of BL-OW's `progBLO` on one input and one world, from the two
contracts (with BL-OW's run). -/
theorem progBLOW_world {xinit xA xM xB : Layout → XCmdO} (K : DrvKO)
    (hS : SetupSpecW xinit K.Cs K.ks K.nSs K.nNs K.nAs) (hR : RoundSpecW xA xM xB K.C K.k K.Cn K.kn K.nS K.nN K.nA)
    {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hI : InU d n δ r0 R0) (w : WorldO d) :
    CostOKO (progBLO xinit xA xM xB K.L) w (initU d n δ r0 R0 a) n (K.cost d n δ r0 R0 a : ℝ) ∧
      SpaceOKO (progBLO xinit xA xM xB K.L) w (initU d n δ r0 R0 a) n (K.space d n δ r0 R0 a : ℝ) ∧
      CoinWindowsOK (progBLO xinit xA xM xB K.L) w (initU d n δ r0 R0 a) n (DO d n δ r0 R0 a)
        (DO' d n δ r0 R0 a) ∧
      ∀ t < n, playedO (progBLO xinit xA xM xB K.L) w (initU d n δ r0 R0 a) t = toE (playOW d n δ r0 R0 a w t) := by
  unfold progBLO
  have hLay : LayOK K.L d (K.ella d n δ r0 R0 a) := K.layOK d n δ r0 R0 a
  have hQ' := K.Q_lt d n δ r0 R0 a
  unfold DrvKO.Q at hQ'
  have hoff : offU d < 2 ^ K.ella d n δ r0 R0 a := by omega
  have h4 : 4 ≤ 2 ^ K.ella d n δ r0 R0 a := by omega
  have hKiA : K.Ki d n δ r0 R0 a < 2 ^ K.ella d n δ r0 R0 a := by omega
  have hKrA : K.Kr d n δ r0 R0 a < 2 ^ K.ella d n δ r0 R0 a := by omega
  have hRs : RoomO K.L K.nSs K.nNs K.nAs := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [DrvKO.L] <;> omega
  have hRr : RoomO K.L K.nS K.nN K.nA := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [DrvKO.L] <;> omega
  have hE0 : K.E0 d n δ r0 R0 a ≤ K.E d n δ r0 R0 a := Nat.le_add_right _ _
  have hEn : K.Cn * (wU d n δ r0 R0 a + K.E0 d n δ r0 R0 a + 1) ^ K.kn ≤ K.E d n δ r0 R0 a :=
    Nat.le_add_left _ _
  have hKi : K.Ki d n δ r0 R0 a ≤ K.ell d n δ r0 R0 a := by unfold DrvKO.ell; omega
  have hKr : K.Kr d n δ r0 R0 a ≤ K.ell d n δ r0 R0 a := by unfold DrvKO.ell; omega
  have hdl : d < K.ell d n δ r0 R0 a := by unfold DrvKO.ell; omega
  -- the setup
  have hsetup0 := hS d K.L w n δ r0 R0 a (K.E d n δ r0 R0 a) (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a) hI hLay
    hRs hE0 hKi hKiA
  have hX0 : (ctxU w n δ r0 R0 a).X.inp 0 = d := inputU_zero (n := n) (δ := δ) (r0 := r0) (R0 := R0) (a := a)
  have hoff1 : 1 ≤ (ctxU w n δ r0 R0 a).X.off := by show 1 ≤ offU d; unfold offU; omega
  have hdlR : (d : ℝ) < 2 ^ K.ell d n δ r0 R0 a := by
    have : d < 2 ^ K.ell d n δ r0 R0 a := hdl.trans Nat.lt_two_pow_self
    exact_mod_cast this
  obtain ⟨s1, e1, r1⟩ := xsetup_exec (X := (ctxU w n δ r0 R0 a).X) (ℓ := K.ell d n δ r0 R0 a) hLay (dv := rD)
    (by simp [DrvKO.L, rD]) (by simp [DrvKO.L]) (by simp [DrvKO.L]) hX0 hoff1 hdlR
  obtain ⟨k2, s2, σ2, hk2, e2, r2, ⟨hinv2, hpos⟩⟩ := hsetup0 s1 r1
  have hsetup : ∃ k s1 σ1, k ≤ K.Ks d n δ r0 R0 a ∧
      XExecBO (ctxU w n δ r0 R0 a) (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a)
        (.seq (.base (xsetup K.L rD)) (xinit K.L)) Unified.ProgO.zeroState k s1 ∧ Rep K.L σ1 s1 ∧
      (BLOInv K.L n (K0O d n δ r0 R0) (K.E d n δ r0 R0 a) (cfgWW d n δ r0 R0 a w) (modeOW d n δ r0 R0 a w 0) 0 σ1 ∧
        CellsW σ1 n δ) := by
    refine ⟨_, s2, σ2, ?_, XExecBO.seq (XExecBO.base e1) e2, r2, hinv2⟩
    unfold DrvKO.Ks DrvKO.Ki
    omega
  -- the rounds
  have hround := fun t (ht : t < n) σ (hσ : BLOInv K.L n (K0O d n δ r0 R0) (K.E d n δ r0 R0 a)
      (cfgWW d n δ r0 R0 a w) (modeOW d n δ r0 R0 a w t) t σ ∧ CellsW σ n δ) =>
    hR d K.L w n δ r0 R0 a (K.E0 d n δ r0 R0 a) (K.E d n δ r0 R0 a) (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a)
      t σ hI ht hLay hRr hpos hEn hKr hKrA hσ.1 hσ.2
  obtain ⟨hC, hSp, hCW, hpl⟩ := progO_ok (L := K.L) (ℓa := K.ella d n δ r0 R0 a) (ℓ := K.ell d n δ r0 R0 a)
    (Inv := fun t σ => BLOInv K.L n (K0O d n δ r0 R0) (K.E d n δ r0 R0 a) (cfgWW d n δ r0 R0 a w)
      (modeOW d n δ r0 R0 a w t) t σ ∧ CellsW σ n δ)
    (IA := fun t σA => σA.rounds = t ∧ σA.draws = DO' d n δ r0 R0 a t ∧
      XRunsBO K.L (ctxU w n δ r0 R0 a) (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a) (xM K.L) σA
        (K.Kr d n δ r0 R0 a) (fun σM =>
        σM.rounds = t + 1 ∧ σM.draws = DO' d n δ r0 R0 a t ∧ σM.pts t = toE (playOW d n δ r0 R0 a w t) ∧
        XRunsBO K.L (ctxU w n δ r0 R0 a) (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a) (xB K.L) σM
          (K.Kr d n δ r0 R0 a) (fun σ' => BLOInv K.L n (K0O d n δ r0 R0) (K.E d n δ r0 R0 a)
            (cfgWW d n δ r0 R0 a w) (modeOW d n δ r0 R0 a w (t + 1)) (t + 1) σ' ∧ CellsW σ' n δ)))
    (IM := fun t σM => σM.rounds = t + 1 ∧ σM.draws = DO' d n δ r0 R0 a t ∧
      σM.pts t = toE (playOW d n δ r0 R0 a w t) ∧
      XRunsBO K.L (ctxU w n δ r0 R0 a) (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a) (xB K.L) σM
        (K.Kr d n δ r0 R0 a) (fun σ' => BLOInv K.L n (K0O d n δ r0 R0) (K.E d n δ r0 R0 a) (cfgWW d n δ r0 R0 a w)
          (modeOW d n δ r0 R0 a w (t + 1)) (t + 1) σ' ∧ CellsW σ' n δ))
    w (K.Ks d n δ r0 R0 a) (K.Kr d n δ r0 R0 a) (K.Kr d n δ r0 R0 a) (K.Kr d n δ r0 R0 a) (DO d n δ r0 R0 a)
    (DO' d n δ r0 R0 a) hoff h4 hsetup
    (fun t ht σ hσ => hround t ht σ hσ) (fun t _ σ hσ => hσ.2.2) (fun t _ σ hσ => hσ.2.2.2)
    (fun t σ hσ => hσ.1.rounds) (fun t σ hσ => ⟨hσ.1, hσ.2.1⟩) (fun t σ hσ => ⟨hσ.1, hσ.2.1⟩)
    (fun t => by
      simp only [DO, DO', AdversarialBco.Unified.World.winL, AdversarialBco.Unified.World.winN, Bit.Sched.blkStart]
      have h1 : 1 ≤ Bit.Sched.nBlk d := by unfold Bit.Sched.nBlk; omega
      have : t * Bit.Sched.nBlk d + (Bit.Sched.nBlk d - 1) ≤ (t + 1) * Bit.Sched.nBlk d + 0 := by
        rw [Nat.add_mul, one_mul]; omega
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) _)
  refine ⟨hC, by simpa only [DrvKO.space, Nat.cast_add, Nat.cast_max] using hSp, hCW, fun t ht => ?_⟩
  obtain ⟨σ, hσ, he⟩ := hpl t ht
  rw [he, hσ.2.2.1]

/-! ## The contracts of BLOSpec.lean for BL-OW -/

/-- **The program link of BL-OW** from the setup and round contracts: the point the program plays in round `t < n`
is BL-OW's pure play `playOW`. -/
theorem bloWLink_of {xinit xA xM xB : Layout → XCmdO} (K : DrvKO)
    (hS : SetupSpecW xinit K.Cs K.ks K.nSs K.nNs K.nAs) (hR : RoundSpecW xA xM xB K.C K.k K.Cn K.kn K.nS K.nN K.nA) :
    ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
      ∀ (w : WorldO d) (t : ℕ), t < n →
        playedO (progBLO xinit xA xM xB K.L) w (initU d n δ r0 R0 a) t = toE (playOW d n δ r0 R0 a w t) := by
  intro d n δ r0 R0 a hd hn hδ0 hδ1 hr0 hR0 w t ht
  exact (progBLOW_world K hS hR a ⟨hd, hn, hδ0, hδ1, hr0, hR0⟩ w).2.2.2 t ht

/-- **`BLOMachOK` for BL-OW's program** from the setup and round contracts. -/
theorem bloWMachOK_of {xinit xA xM xB : Layout → XCmdO} (K : DrvKO)
    (hS : SetupSpecW xinit K.Cs K.ks K.nSs K.nNs K.nAs) (hR : RoundSpecW xA xM xB K.C K.k K.Cn K.kn K.nS K.nN K.nA) :
    ∃ (C' : ℝ) (k : ℕ), BLOMachOK (progBLO xinit xA xM xB K.L) C' k := by
  obtain ⟨c, k, hck⟩ := drvO_poly K
  refine ⟨c * (4 / Real.log 2) ^ k, k, fun d n δ r0 R0 a hd hn hδ0 hδ1 hr0 hR0 w => ?_⟩
  have hI : InU d n δ r0 R0 := ⟨hd, hn, hδ0, hδ1, hr0, hR0⟩
  obtain ⟨hC, hSp, hCW, -⟩ := progBLOW_world K hS hR a hI w
  obtain ⟨h1, h2⟩ := hck d n δ r0 R0 a hI
  have hf := frozenO_form a hI c k
  have e1 : (K.cost d n δ r0 R0 a : ℝ) ≤ c * (wU d n δ r0 R0 a : ℝ) ^ k := by exact_mod_cast h1
  have e2 : (K.space d n δ r0 R0 a : ℝ) ≤ c * (wU d n δ r0 R0 a : ℝ) ^ k := by exact_mod_cast h2
  exact ⟨costOKO_mono hC (e1.trans hf), spaceOKO_mono hSp (e2.trans hf), hCW⟩

/-- The setup contract of BL-OW for some command and constants. -/
def ProgSetupW : Prop := ∃ (xinit : Layout → XCmdO) (C k nS nN nA : ℕ), SetupSpecW xinit C k nS nN nA

/-- The round contract of BL-OW for some commands and constants. -/
def ProgRoundW : Prop :=
  ∃ (xA xM xB : Layout → XCmdO) (C k Cn kn nS nN nA : ℕ), RoundSpecW xA xM xB C k Cn kn nS nN nA

/-- **BL-OW's program from its two contracts**: some program of the oracle machine plays BL-OW's pure plays and
meets the machine clauses of `TheoremUW` with BL-O's windows. -/
theorem theoremProgW_of (hS : ProgSetupW) (hR : ProgRoundW) :
    ∃ (P : List InstrO) (C' : ℝ) (k : ℕ),
      (∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
        ∀ (w : WorldO d) (t : ℕ), t < n → playedO P w (initU d n δ r0 R0 a) t = toE (playOW d n δ r0 R0 a w t)) ∧
      BLOMachOK P C' k := by
  obtain ⟨xinit, Cs, ks, nSs, nNs, nAs, hS⟩ := hS
  obtain ⟨xA, xM, xB, C, k, Cn, kn, nS, nN, nA, hR⟩ := hR
  let K : DrvKO := ⟨Cs, ks, nSs, nNs, nAs, C, k, Cn, kn, nS, nN, nA⟩
  obtain ⟨C', k', hM⟩ := bloWMachOK_of K hS hR
  exact ⟨_, C', k', bloWLink_of K hS hR, hM⟩

end AdversarialBco.UW.ProgW
