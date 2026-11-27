/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSetupP0
public import AdversarialBco.Unified.ProgOTst
public import AdversarialBco.Unified.PrmKLink
public import AdversarialBco.Bit.Transfer.XTriBox

@[expose] public section

/-!
# BL-O's setup: the cross check

`xcrossO`: the constants of the CM precision `kC` (`xcmc` of ProgOTst.lean, test layout `qX`: slots from
`30`, registers from `16`, arrays from `8`), then the flag `sBadS := 0`, the point array `12` at `(2; 0)`, and for
`i < d` the two tests of `xtst` at the points `(2; e_i)`, `(2; -e_i)` of the array `12`, i.e. BL-O's test at
`μ_S ± A_S e_i/2`, each setting the flag to `1` when it rejects. `crossSpecO`: `CrossSpecO` for it.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.BudK (parK)
open AdversarialBco.BitRAM (len)

variable {d : ℕ}

/-! ## The program -/

/-- The test layout of the cross check: slots from `30`, registers from `16`, arrays from `8`. -/
def qX : TstLay := ⟨30, 16, 8⟩

/-- The start: `33 := 0 - 1`, `sBadS := 0`, the cells `0, ..., d` of the array `12` at `0`, then its cell `0` at `2`. -/
def xcrossI (L : Layout) : XCmd :=
  .seq (toX (VL.sop2 L .sub 33 sZ 26)) <| .seq (toX (VL.sconst L sBadS 0)) <|
  .seq (xzero L 12 sZ 43 rD rOne) <| .seq (toX (VL.aset L 12 rD sZ)) <|
  .seq (.prim (.frag (.nconst 44 0))) (toX (VL.aset L 12 44 27))

/-- `sBadS := 1` if the test's answer in the register `41` is `0`. -/
def xflagO (L : Layout) : XCmdO := .ifN 41 rOne (.base (toX (VL.sconst L sBadS 1))) (.base .skip)

/-- One test of the cross check: the point of the array `12`, the flag. -/
def xcrossT (L : Layout) : XCmdO := .seq (xtst L qX 12 41) (xflagO L)

/-- Turn `i` (register `40`): the cell `i + 1` of the array `12` at `1`, the test, at `-1`, the test, back at `0`. -/
def xcrossB (L : Layout) : XCmdO :=
  .seq (.base (.seq (.prim (.frag (.nadd 42 40 rOne))) (toX (VL.aset L 12 42 26)))) <|
  .seq (xcrossT L) <| .seq (.base (toX (VL.aset L 12 42 33))) <| .seq (xcrossT L) (.base (toX (VL.aset L 12 42 sZ)))

/-- **The cross check of BL-O's setup.** -/
def xcrossO (L : Layout) : XCmdO :=
  .seq (.base (xcmc L qX)) (.seq (.base (xcrossI L)) (xforNO 40 rD rOne (xcrossB L)))

/-! ## Facts -/

theorem ptDN_single (i : Fin d) (c : ℤ) : ptDN 2 (Pi.single i c) = Pi.single i ((c : ℚ) / 2) := by
  funext j
  by_cases h : j = i
  · subst h; simp [ptDN]
  · simp [ptDN, Pi.single_apply, h]

theorem cmcK_le {p e : ℕ} {N D : ℤ} (hN : 0 ≤ N) (hD : 0 < D) (hNe : N ≤ 2 ^ e) : cmcK p N D ≤ p + e + 4 := by
  unfold cmcK
  obtain ⟨-, h1⟩ := ceil_quot_le hN hD
  have h2 : (0 - (0 - N) / D).toNat ≤ 2 ^ e := by
    rw [Int.toNat_le]; push_cast; linarith
  have h3 := Nat.clog_le_of_le_pow h2
  omega

/-- The data of the test block survive a frame that avoids its cells. -/
theorem TstDat.frame {Q : TstLay} {DS : ℤ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ} {Da : ℤ}
    {Na : Fin d → ℤ} {rn rd : ℤ} {k : ℕ} {σ σ' : Env d} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop}
    (h : TstDat Q DS muS aS Da Na rn rd k σ) (F : FrameA S N Ar σ σ')
    (hS : ¬ S sZ ∧ ¬ S sDS ∧ ¬ S Q.s ∧ ¬ S (Q.s + 1) ∧ ¬ S (Q.s + 2)) (hN : ¬ N rD ∧ ¬ N rOne ∧ ¬ N Q.n)
    (hA : ∀ k, ¬ Ar aMuS k ∧ ¬ Ar aAS k ∧ ¬ Ar aC k) : TstDat Q DS muS aS Da Na rn rd k σ' := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := hS
  obtain ⟨n1, n2, n3⟩ := hN
  obtain ⟨hd, h1, hz, hds, hmu, has, hcm⟩ := h
  refine ⟨(F.1 _ n1).trans hd, (F.1 _ n2).trans h1, (F.2.1 _ s1).trans hz, (F.2.1 _ s2).trans hds,
    fun i => (F.2.2.1 _ _ (hA _).1).trans (hmu i), fun i j => (F.2.2.1 _ _ (hA _).2.1).trans (has i j), ?_⟩
  unfold CMDat at hcm ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcm
  exact ⟨(F.2.2.1 _ _ (hA _).2.2).trans c1, fun i => (F.2.2.1 _ _ (hA _).2.2).trans (c2 i), (F.2.1 _ s3).trans c3,
    (F.2.1 _ s4).trans c4, (F.1 _ n3).trans c5, (F.2.1 _ s5).trans c6⟩

/-! ## The blocks -/

theorem XV.crossI {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 86 ≤ L.NS)
    (hNN : 48 ≤ L.NN) (hNA : 16 ≤ L.NA) (hd1 : 1 ≤ d) (hz : σ.sc sZ = 0) (h26 : σ.sc 26 = 1) (h27 : σ.sc 27 = 2)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hℓ : 2 < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xcrossI L) σ (1 + (1 + ((d * (2 + 3) + 3) + (2 + (1 + 2))))) (fun σ' =>
      σ'.sc 33 = -1 ∧ σ'.sc sBadS = 0 ∧ σ'.arr 12 0 = 2 ∧ (∀ j : Fin d, σ'.arr 12 (1 + (j : ℕ)) = 0) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = 33 ∨ y = sBadS) (fun j => j = 43 ∨ j = 44) (fun b _ => b = 12) σ σ') := by
  have h2l : (2 : ℝ) < 2 ^ ℓ := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
  refine XV.seq (XV.sop2 hL (x := 33) (a := sZ) (b := 26) (by omega) (by suomega) (by omega) .sub
    (by intro h; cases h) (by rw [hz]; simp) (by rw [h26]; simp; linarith)
    (by simp only [RealRAM.Op2.eval, hz, h26]; norm_num; linarith)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.sconst hL (x := sBadS) (by suomega) 0 rfl (by simp)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.zero hL (aR := 12) (sZ := sZ) (nl := 43) (nd := rD) (none := rOne) (by omega) (by suomega)
    (by omega) (by suomega) (by suomega) (by decide) (by simpa using hD) (by simpa using h1) hda
    (by simp [hz])) fun σ3 ⟨z3, d3, F3⟩ => ?_
  have n3 : σ3.nat rD = d := by rw [F3.1 rD (by decide)]; simpa using hD
  have s3 : ∀ y, σ3.sc y = _ := fun y => F3.2.1 y id
  refine XV.seq (XV.aset hL (a := 12) (i := rD) (x := sZ) (by omega) (by suomega) (by suomega)
    (by rw [n3]; unfold asz; nlinarith) (by rw [s3]; simp [hz])) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.nconst hL (i := 44) (by omega) 0 (by positivity)) fun σ5 e5 => ?_
  subst e5
  refine XV.mono (XV.aset hL (a := 12) (i := 44) (x := 27) (by omega) (by omega) (by omega)
    (by rw [Env.setNat_nat, if_pos rfl]; unfold asz; nlinarith)
    (by simp only [Env.setNat_sc, Env.setArr_sc, s3]; simp [h27]; linarith)) le_rfl fun σ6 e6 => ?_
  subst e6
  refine ⟨?_, ?_, ?_, fun j => ?_, ?_, ?_⟩
  · simp only [Env.setArr_sc, Env.setNat_sc, s3]; simp [RealRAM.Op2.eval, hz, h26]
  · simp only [Env.setArr_sc, Env.setNat_sc, s3]; simp
  · simp only [Env.setArr_arr, Env.setNat_arr, Env.setNat_nat, Env.setNat_sc, Env.setArr_sc, s3]; simp [h27]
  · have hj := j.2
    rw [Env.setArr_arr, if_neg (by simp), Env.setNat_arr, Env.setArr_arr, n3]
    by_cases hjd : 1 + (j : ℕ) = d
    · rw [if_pos ⟨rfl, hjd⟩, s3]; simp [hz]
    · rw [if_neg (fun h => hjd h.2)]
      exact z3 _ (by omega)
  · simp only [Env.setArr_draws, Env.setNat_draws, d3, Env.setSc_draws]
  · have F2 : FrameA (fun y => y = 33 ∨ y = sBadS) (fun j => j = 43 ∨ j = 44) (fun b _ => b = 12) σ
        ((σ.setSc 33 (RealRAM.Op2.eval .sub (σ.sc sZ) (σ.sc 26))).setSc sBadS ((0 : ℚ) : ℝ)) :=
      ((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setSc (Or.inr rfl) _
    exact (((F2.trans (F3.mono (fun _ h => h.elim) (fun _ h => Or.inl h) fun _ _ h => h.1)).setArr rfl _).setNat
      (Or.inr rfl) _).setArr rfl _

theorem XVO.flag {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 30 ≤ L.NS) (hNN : 42 ≤ L.NN)
    {σ : Env d} {P : Prop} [Decidable P] {b : Bool} (h1 : σ.nat rOne = 1)
    (hf : σ.sc sBadS = ((if P then 0 else 1 : ℤ) : ℝ)) (ht : σ.nat 41 = if b = true then 1 else 0) (hℓ : 1 < ℓ) :
    XRunsBO L XO ℓa ℓ (xflagO L) σ 3 (fun σ' => σ'.sc sBadS = ((if P ∧ b = true then 0 else 1 : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA (fun y => y = sBadS) (fun _ => False) (fun _ _ => False) σ σ') := by
  have h2a : 1 < 2 ^ ℓa := by have := hL.1; omega
  have h1l : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by
    rw [Rat.cast_one, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  refine XVO.ifN hL (by omega) (by suomega) (by rw [ht]; split_ifs <;> omega) (by rw [h1]; omega)
    (fun hc => ?_) (fun hc => ?_)
  · have hb : b = false := by
      rw [ht, h1] at hc; cases b <;> simp_all
    refine XVO.ofX (XV.mono (XV.sconst hL (x := sBadS) (by suomega) 1 rfl h1l) le_rfl fun σ' e => ?_)
    subst e
    exact ⟨by simp [hb], rfl, (FrameA.refl (fun y => y = sBadS) (fun _ => False) (fun _ _ => False) σ).setSc rfl _⟩
  · have hb : b = true := by
      rw [ht, h1] at hc; cases b <;> simp_all
    refine XVO.ofX (XV.mono (XV.skip σ) (by omega) fun σ' e => ?_)
    subst e
    exact ⟨by rw [hf]; simp [hb], rfl, FrameA.refl _ _ _ _⟩

/-! ## A turn -/

/-- The slots a turn writes: the flag and the slots from `46`. -/
abbrev sXB (y : ℕ) : Prop := y = sBadS ∨ 46 ≤ y

/-- The registers a turn writes: `41`, `42` and `17, ..., 26`. -/
abbrev nXB (j : ℕ) : Prop := j = 41 ∨ j = 42 ∨ (17 ≤ j ∧ j < 27)

/-- The arrays a turn writes: `8, ..., 12`. -/
abbrev aXB (b _k : ℕ) : Prop := 8 ≤ b ∧ b ≤ 12

/-- A point `(2; c e_i)` in the array `12` from the cells `0, ..., d` of `σ` at `(2; 0)` and the cell `i + 1` at `c`. -/
theorem pt_of {σ σx : Env d} {i : Fin d} (c : ℤ)
    (h : ∀ k, σx.arr 12 k = if k = (i : ℕ) + 1 then ((c : ℤ) : ℝ) else σ.arr 12 k)
    (a0 : σ.arr 12 0 = 2) (az : ∀ j : Fin d, σ.arr 12 (1 + (j : ℕ)) = 0) :
    σx.arr 12 0 = 2 ∧ ∀ j : Fin d, σx.arr 12 (1 + (j : ℕ)) = (((Pi.single i c : Fin d → ℤ) j : ℤ) : ℝ) := by
  refine ⟨by rw [h, if_neg (by omega), a0], fun j => ?_⟩
  rw [h]
  by_cases hj : j = i
  · subst hj; rw [if_pos (by omega), Pi.single_eq_same]
  · rw [if_neg (fun e => hj (Fin.ext (by omega))), az, Pi.single_eq_of_ne hj]; simp

/-- **One test**: from the test block's data and the point `(2; c e_i)` in the array `12`, the flag `P` becomes
`P ∧ T(c e_i/2)`. -/
theorem XVO.crossT {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 86 ≤ L.NS)
    (hNN : 48 ≤ L.NN) (hNA : 16 ≤ L.NA) (hd1 : 1 ≤ d)
    {DS : ℤ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {k m : ℕ}
    (hDS : 0 < DS) (bDS : DS ≤ 2 ^ m) (bmu : ∀ i, |muS i| ≤ 2 ^ m) (baS : ∀ i j, |aS i j| ≤ 2 ^ m)
    (hdm : d ≤ 2 ^ m) (hDa : 0 < Da) (bDa : Da < 2 ^ m) (bNa : ∀ i, |Na i| < 2 ^ m) (hrn : 0 < rn)
    (brn : rn < 2 ^ m) (hrd : 0 < rd) (brd : rd < 2 ^ m) (hℓ : 6 * m + 2 * 2 + k + 12 ≤ ℓ) (hk : k < 2 ^ ℓa)
    {P : Prop} [Decidable P] {σ : Env d} (i : Fin d) (c : ℤ) (hc : |c| ≤ 1)
    (hdat : TstDat qX DS muS aS Da Na rn rd k σ) (p0 : σ.arr 12 0 = 2)
    (pj : ∀ j : Fin d, σ.arr 12 (1 + (j : ℕ)) = (((Pi.single i c : Fin d → ℤ) j : ℤ) : ℝ))
    (hf : σ.sc sBadS = ((if P then 0 else 1 : ℤ) : ℝ)) :
    XRunsBO L XO ℓa ℓ (xcrossT L) σ (tstK d + 3) (fun σ' =>
      σ'.sc sBadS = ((if P ∧ cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k
        (pmap DS muS aS (Pi.single i ((c : ℚ) / 2))) = true then 0 else 1 : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA sXB nXB aXB σ σ' ∧ σ'.nat 42 = σ.nat 42 ∧ (∀ k, σ'.arr 12 k = σ.arr 12 k)) := by
  have hQ : qX.OK L := ⟨⟨by simp [qX], by simp only [qX]; omega⟩, ⟨by simp [qX], by simp only [qX]; omega⟩,
    ⟨by simp [qX], by simp only [qX]; omega⟩⟩
  have bNv : ∀ j, |(Pi.single i c : Fin d → ℤ) j| < 2 ^ 2 := fun j => by
    by_cases hj : j = i
    · subst hj; rw [Pi.single_eq_same]; linarith
    · rw [Pi.single_eq_of_ne hj]; norm_num
  refine XVO.seq (tstOK (XO := XO) (ℓ := ℓ) hL hQ (ap := 12) (nt := 41) (by omega) (Or.inr (by simp [qX]))
    (by omega) (by omega) (Or.inr (by simp [qX])) hd1 hDS bDS bmu baS hdm hDa bDa bNa hrn brn hrd brd hℓ hk σ 2
    (Pi.single i c) hdat (by norm_num) (by norm_num) bNv (by rw [p0]; norm_num) pj) fun σ1 ⟨t1, F1, d1⟩ => ?_
  have h1 : σ1.nat rOne = 1 := (F1.1 rOne (by decide)).trans hdat.h1
  have f1 : σ1.sc sBadS = ((if P then 0 else 1 : ℤ) : ℝ) := (F1.2.1 sBadS (by decide)).trans hf
  have t1' : σ1.nat 41 = if cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k
      (pmap DS muS aS (Pi.single i ((c : ℚ) / 2))) = true then 1 else 0 := by
    rw [t1, ptDN_single]
  refine XVO.mono (XVO.flag hL (by omega) (by omega) h1 f1 t1' (by omega)) le_rfl fun σ2 ⟨f2, d2, F2⟩ => ?_
  have F1' : FrameA sXB nXB aXB σ σ1 := F1.mono (fun y h => Or.inr (by simp only [qX] at h; omega))
    (fun j h => h.elim Or.inl fun h => Or.inr (Or.inr (by simp only [qX] at h; omega)))
    (fun b _ h => by simp only [qX] at h; omega)
  have F2' : FrameA sXB nXB aXB σ1 σ2 := F2.mono (fun _ h => Or.inl h) (fun _ h => h.elim) fun _ _ h => h.elim
  refine ⟨f2, d2.trans d1, F1'.trans F2', ?_, fun k => ?_⟩
  · rw [F2.1 42 id, F1.1 42 (by simp [qX])]
  · rw [F2.2.2.1 12 k id, F1.2.2.1 12 k (by simp [qX])]

/-- **A turn**: the tests at `(2; e_i)` and `(2; -e_i)`, the flag `P` becomes `P ∧ T(e_i/2) ∧ T(-e_i/2)`. -/
theorem XVO.crossB {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 86 ≤ L.NS)
    (hNN : 48 ≤ L.NN) (hNA : 16 ≤ L.NA) (hd1 : 1 ≤ d)
    {DS : ℤ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {k m : ℕ}
    (hDS : 0 < DS) (bDS : DS ≤ 2 ^ m) (bmu : ∀ i, |muS i| ≤ 2 ^ m) (baS : ∀ i j, |aS i j| ≤ 2 ^ m)
    (hdm : d ≤ 2 ^ m) (hDa : 0 < Da) (bDa : Da < 2 ^ m) (bNa : ∀ i, |Na i| < 2 ^ m) (hrn : 0 < rn)
    (brn : rn < 2 ^ m) (hrd : 0 < rd) (brd : rd < 2 ^ m) (hℓ : 6 * m + 2 * 2 + k + 12 ≤ ℓ) (hk : k < 2 ^ ℓa)
    (hda : d * d + d < 2 ^ ℓa) {P : Prop} [Decidable P] {σ : Env d} (i : Fin d)
    (hdat : TstDat qX DS muS aS Da Na rn rd k σ) (h40 : σ.nat 40 = i) (a0 : σ.arr 12 0 = 2)
    (az : ∀ j : Fin d, σ.arr 12 (1 + (j : ℕ)) = 0) (s33 : σ.sc 33 = -1) (s26 : σ.sc 26 = 1)
    (hf : σ.sc sBadS = ((if P then 0 else 1 : ℤ) : ℝ)) :
    XRunsBO L XO ℓa ℓ (xcrossB L) σ (2 * tstK d + 13) (fun σ' =>
      TstDat qX DS muS aS Da Na rn rd k σ' ∧ σ'.arr 12 0 = 2 ∧ (∀ j : Fin d, σ'.arr 12 (1 + (j : ℕ)) = 0) ∧
      σ'.sc 33 = -1 ∧ σ'.sc 26 = 1 ∧
      σ'.sc sBadS = ((if (P ∧ cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k
        (pmap DS muS aS (Pi.single i (((1 : ℤ) : ℚ) / 2))) = true) ∧ cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k
        (pmap DS muS aS (Pi.single i (((-1 : ℤ) : ℚ) / 2))) = true then 0 else 1 : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA sXB nXB aXB σ σ') := by
  have hi := i.2
  have h1 := hdat.h1
  have datB : ∀ σ', FrameA sXB nXB aXB σ σ' → TstDat qX DS muS aS Da Na rn rd k σ' := fun σ' F =>
    hdat.frame F (by decide) (by decide) fun _ => by (try simp only [aXB, aMuS, aAS, aC]) <;> omega
  have hu : (1 : ℝ) < 2 ^ ℓ := one_lt_pow₀ (by norm_num) (by omega)
  refine XVO.mono (K := (1 + 2) + ((tstK d + 3) + (2 + ((tstK d + 3) + 2)))) ?_ (by omega) fun _ h => h
  -- the point `(2; e_i)`
  have hA : XRunsB L XO.X ℓa ℓ (.seq (.prim (.frag (.nadd 42 40 rOne))) (toX (VL.aset L 12 42 26))) σ (1 + 2)
      (· = (σ.setNat 42 ((i : ℕ) + 1)).setArr 12 ((i : ℕ) + 1) ((1 : ℤ) : ℝ)) := by
    refine XV.seq (XV.nadd hL (i := 42) (a := 40) (b := rOne) (by omega) (by omega) (by suomega)
      (by rw [h40]; omega) (by rw [h1]; omega)) fun σa ea => ?_
    subst ea
    refine XV.mono (XV.aset hL (a := 12) (i := 42) (x := 26) (by omega) (by omega) (by omega) ?_ ?_) le_rfl
      fun σb eb => ?_
    · rw [Env.setNat_nat, if_pos rfl, h40, h1]; unfold asz; nlinarith
    · rw [Env.setNat_sc, s26, abs_one]; exact hu
    · rw [eb, Env.setNat_nat, if_pos rfl, h40, h1, Env.setNat_sc, s26, Int.cast_one]
  refine XVO.seq (XVO.ofX hA) fun σb eb => ?_
  subst eb
  have Fb : FrameA sXB nXB aXB σ ((σ.setNat 42 ((i : ℕ) + 1)).setArr 12 ((i : ℕ) + 1) ((1 : ℤ) : ℝ)) :=
    ((FrameA.refl _ _ _ σ).setNat (by decide) _).setArr ⟨by norm_num, le_rfl⟩ _
  obtain ⟨p0b, pjb⟩ := pt_of (σ := σ) (i := i) 1 (fun k => by
    rw [Env.setArr_arr, Env.setNat_arr]
    by_cases hk : k = (i : ℕ) + 1
    · rw [if_pos ⟨rfl, hk⟩, if_pos hk]
    · rw [if_neg (fun h => hk h.2), if_neg hk]) a0 az
  refine XVO.seq (XVO.crossT hL hNS hNN hNA hd1 hDS bDS bmu baS hdm hDa bDa bNa hrn brn hrd brd hℓ hk (P := P) i 1
    (by norm_num) (datB _ Fb) p0b pjb (by rw [Env.setArr_sc, Env.setNat_sc]; exact hf))
    fun σc ⟨fc, dc, Fc, nc, ac⟩ => ?_
  -- the point `(2; -e_i)`
  have Fbc := Fb.trans Fc
  have n42c : σc.nat 42 = (i : ℕ) + 1 := by rw [nc, Env.setArr_nat, Env.setNat_nat, if_pos rfl]
  have s33c : σc.sc 33 = -1 := by rw [Fbc.2.1 33 (by decide), s33]
  refine XVO.seq (XVO.ofX (XV.aset hL (a := 12) (i := 42) (x := 33) (by omega) (by omega) (by omega)
    (by rw [n42c]; unfold asz; nlinarith) (by rw [s33c, abs_neg, abs_one]; exact hu))) fun σe ee => ?_
  subst ee
  rw [n42c, s33c]
  have Fe : FrameA sXB nXB aXB σ (σc.setArr 12 ((i : ℕ) + 1) (-1)) := Fbc.setArr ⟨by norm_num, le_rfl⟩ _
  obtain ⟨p0e, pje⟩ := pt_of (σ := σ) (σx := σc.setArr 12 ((i : ℕ) + 1) (-1)) (i := i) (-1) (fun k => by
    rw [Env.setArr_arr]
    by_cases hk : k = (i : ℕ) + 1
    · rw [if_pos ⟨rfl, hk⟩, if_pos hk]; simp
    · rw [if_neg (fun h => hk h.2), ac, Env.setArr_arr, Env.setNat_arr, if_neg (fun h => hk h.2), if_neg hk]) a0 az
  refine XVO.seq (XVO.crossT hL hNS hNN hNA hd1 hDS bDS bmu baS hdm hDa bDa bNa hrn brn hrd brd hℓ hk i (-1)
    (by norm_num) (datB _ Fe) p0e pje ((congrFun (Env.setArr_sc σc 12 _ _) sBadS).trans fc))
    fun σf ⟨ff, df, Ff, nf, af⟩ => ?_
  -- back at `0`
  have Fef := Fe.trans Ff
  have n42f : σf.nat 42 = (i : ℕ) + 1 := by rw [nf, Env.setArr_nat, n42c]
  have szf : σf.sc sZ = 0 := by rw [Fef.2.1 sZ (by decide)]; exact hdat.hz
  refine XVO.mono (XVO.ofX (XV.aset hL (a := 12) (i := 42) (x := sZ) (by omega) (by omega) (by suomega)
    (by rw [n42f]; unfold asz; nlinarith) (by rw [szf]; simp))) le_rfl fun σh eh => ?_
  subst eh
  rw [n42f, szf]
  have Fh : FrameA sXB nXB aXB σ (σf.setArr 12 ((i : ℕ) + 1) 0) := Fef.setArr ⟨by norm_num, le_rfl⟩ _
  obtain ⟨p0h, pjh⟩ := pt_of (σ := σ) (σx := σf.setArr 12 ((i : ℕ) + 1) 0) (i := i) 0 (fun k => by
    rw [Env.setArr_arr]
    by_cases hk : k = (i : ℕ) + 1
    · rw [if_pos ⟨rfl, hk⟩, if_pos hk]; simp
    · rw [if_neg (fun h => hk h.2), af, Env.setArr_arr, if_neg (fun h => hk h.2), ac, Env.setArr_arr,
        Env.setNat_arr, if_neg (fun h => hk h.2), if_neg hk]) a0 az
  refine ⟨datB _ Fh, p0h, fun j => by rw [pjh j]; simp, by rw [Fh.2.1 33 (by decide), s33],
    by rw [Fh.2.1 26 (by decide), s26], by rw [Env.setArr_sc]; exact ff, ?_, Fh⟩
  rw [Env.setArr_draws, df, Env.setArr_draws, dc, Env.setArr_draws, Env.setNat_draws]

/-! ## The cross check -/

set_option maxHeartbeats 4000000 in
/-- **The cross check on the machine**: `CrossSpecO` for `xcrossO`, within `2000 (W + s + 1)^3` units. -/
theorem crossSpecO : CrossSpecO xcrossO 2000 3 172 48 16 := by
  intro d L w n δ r0 R0 a ℓa ℓ s S σ hI hL hR hB hP hSB hPos hCtr hℓ hℓa
  obtain ⟨hNS, hNN, hNA⟩ := hR
  have hd := hI.hd
  obtain ⟨b0, b1, bz, -, b26, b27, -⟩ := hB
  have hdW : d + sizeN δ r0 R0 a ≤ wU d n δ r0 R0 a := by unfold wU; omega
  set W := wU d n δ r0 R0 a with hW
  set m := s + W with hm
  -- the units
  have hX1 : 1 ≤ W + s + 1 := by omega
  have e1 : d * d ≤ (W + s + 1) * (W + s + 1) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : d * d * d ≤ (W + s + 1) * (W + s + 1) * (W + s + 1) := Nat.mul_le_mul e1 (by omega)
  have e3 : (W + s + 1) * 1 ≤ (W + s + 1) * (W + s + 1) := Nat.mul_le_mul_left _ hX1
  have e4 : (W + s + 1) * (W + s + 1) * 1 ≤ (W + s + 1) * (W + s + 1) * (W + s + 1) := Nat.mul_le_mul_left _ hX1
  have hX3 : (W + s + 1) ^ 3 = (W + s + 1) * (W + s + 1) * (W + s + 1) := by ring
  rw [hX3] at hℓ hℓa ⊢
  have htK : d * ((2 * tstK d + 13) + 3) = 20 * (d * d * d) + 124 * (d * d) + 182 * d := by
    unfold tstK cmK; ring
  have hda : d * d + d < 2 ^ ℓa := by omega
  -- the inputs
  have hr0 := hI.hr0
  have hrn : 0 < r0.num := Rat.num_pos.2 hr0
  have hR0n : 0 < R0.num := Rat.num_pos.2 (hr0.trans_le hI.hR0)
  have hrd : (0 : ℤ) < r0.den := by exact_mod_cast r0.den_pos
  have hR0d : (0 : ℤ) < R0.den := by exact_mod_cast R0.den_pos
  have hS4 : len r0.num + len (r0.den : ℤ) + len R0.num + len (R0.den : ℤ) ≤ sizeN δ r0 R0 a := by
    unfold sizeN; omega
  have pm : ∀ {e : ℕ}, e ≤ m → (2 : ℤ) ^ e ≤ 2 ^ m := fun h => pow_le_pow_right₀ (by norm_num) h
  have bl : ∀ z : ℤ, len z ≤ m → z < 2 ^ m := fun z h =>
    ((le_abs_self z).trans_lt (abs_lt_len z)).trans_le (pm h)
  have brn := bl r0.num (by omega)
  have brd := bl (r0.den : ℤ) (by omega)
  have bR0n := bl R0.num (by omega)
  have bR0d := bl (R0.den : ℤ) (by omega)
  have hdm : d ≤ 2 ^ m := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- PARAM's values
  obtain ⟨zR, hzR, bR⟩ := hSB sR (by decide) (by decide)
  obtain ⟨zF, hzF, bF⟩ := hSB s2pF (by decide) (by decide)
  obtain ⟨zp, hzp, bp⟩ := hSB s2p (by decide) (by decide)
  have hR' : σ.sc sR = ((qn (parO d n δ).pF (parO d n δ).R : ℤ) : ℝ) := hP.par.2.2.2.2.2.2.1
  have hF' : σ.sc s2pF = (((2 : ℤ) ^ (parO d n δ).pF : ℤ) : ℝ) := by rw [hP.consts.2.1]; push_cast; rfl
  have hp' : σ.sc s2p = (((2 : ℤ) ^ (parO d n δ).p : ℤ) : ℝ) := by rw [hP.consts.1]; push_cast; rfl
  obtain rfl := int_of_sc hzR hR'
  obtain rfl := int_of_sc hzF hF'
  obtain rfl := int_of_sc hzp hp'
  have hRn : 0 ≤ qn (parO d n δ).pF (parO d n δ).R := by
    show 0 ≤ qn (parK d n (kDel δ)).pF (parK d n (kDel δ)).R
    rw [PrmK.qn_parK_R]; exact PrmK.RZK_nonneg
  have bRn : qn (parO d n δ).pF (parO d n δ).R ≤ 2 ^ m := ((le_abs_self _).trans bR).trans (pm (by omega))
  have bPF : (2 : ℤ) ^ (parO d n δ).pF ≤ 2 ^ m := ((le_abs_self _).trans bF).trans (pm (by omega))
  have hps : (parO d n δ).p ≤ s :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 ((le_abs_self _).trans bp)
  -- the position and the centre
  obtain ⟨DS, hDS0, hDSs, hDSo, hmuE, hAE⟩ := hPos
  choose muS hmuS using hmuE
  choose aS haS using hAE
  obtain ⟨Da, hDa0, hDas, hDao, hNaE⟩ := hCtr
  choose Na hNa using hNaE
  have ps : (2 : ℤ) ^ s ≤ 2 ^ m := pm (by omega)
  have bDS : DS ≤ 2 ^ m := hDSs.le.trans ps
  have bmu : ∀ i, |muS i| ≤ 2 ^ m := fun i => (hmuS i).1.le.trans ps
  have baS : ∀ i j, |(aS : Matrix (Fin d) (Fin d) ℤ) i j| ≤ 2 ^ m := fun i j => (haS i j).1.le.trans ps
  have bDa : Da < 2 ^ m := hDas.trans_le ps
  have bNa : ∀ i, |Na i| < 2 ^ m := fun i => (hNa i).1.trans_le ps
  -- the precision
  have hOnG : OnG (cfgS n δ r0 R0 a S).par.pF (cfgS n δ r0 R0 a S).par.R := by
    show ((qn (parK d n (kDel δ)).pF (parK d n (kDel δ)).R : ℤ) : ℚ) =
      (parK d n (kDel δ)).R * 2 ^ (parK d n (kDel δ)).pF
    rw [PrmK.qn_parK_R, PrmK.parK_R_eq]; field_simp
  have hKC : (cfgS n δ r0 R0 a S).kC = cmcK (parO d n δ).p (6 * qn (parO d n δ).pF (parO d n δ).R * R0.num *
      (r0.den : ℤ) * r0.den) (2 ^ (parO d n δ).pF * (R0.den : ℤ) * r0.num * r0.num) :=
    kC_eq (cfgS n δ r0 R0 a S) hOnG hr0
  have hN0 : 0 ≤ 6 * qn (parO d n δ).pF (parO d n δ).R * R0.num * (r0.den : ℤ) * r0.den :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hRn) hR0n.le) hrd.le) hrd.le
  have hD0 : 0 < 2 ^ (parO d n δ).pF * (R0.den : ℤ) * r0.num * r0.num :=
    mul_pos (mul_pos (mul_pos (by positivity) hR0d) hrn) hrn
  have bN : 6 * qn (parO d n δ).pF (parO d n δ).R * R0.num * (r0.den : ℤ) * r0.den ≤ 2 ^ (4 * m + 3) := by
    have e : (2 : ℤ) ^ (4 * m + 3) = 8 * 2 ^ m * 2 ^ m * 2 ^ m * 2 ^ m := by ring
    rw [e]
    exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (by norm_num) bRn hRn (by norm_num)) bR0n.le hR0n.le
      (by positivity)) brd.le hrd.le (by positivity)) brd.le hrd.le (by positivity)
  have hKb : cmcK (parO d n δ).p (6 * qn (parO d n δ).pF (parO d n δ).R * R0.num * (r0.den : ℤ) * r0.den)
      (2 ^ (parO d n δ).pF * (R0.den : ℤ) * r0.num * r0.num) ≤ s + 4 * m + 7 :=
    (cmcK_le hN0 hD0 bN).trans (by omega)
  -- the test layout
  have hQ : qX.OK L := ⟨⟨by simp [qX], by simp only [qX]; omega⟩, ⟨by simp [qX], by simp only [qX]; omega⟩,
    ⟨by simp [qX], by simp only [qX]; omega⟩⟩
  refine XVO.mono (K := 200 * (m + 1) + ((1 + (1 + ((d * (2 + 3) + 3) + (2 + (1 + 2))))) +
    (d * ((2 * tstK d + 13) + 3) + 3))) ?_ (by omega) fun _ h => h
  -- the constants of `kC`
  refine XVO.seq (XVO.ofX (XV.cmc hL hQ (rn := r0.num) (rd := (r0.den : ℤ)) (Rn0 := R0.num) (Rd0 := (R0.den : ℤ))
    (Rn := qn (parO d n δ).pF (parO d n δ).R) (PF := 2 ^ (parO d n δ).pF) (p := (parO d n δ).p) (m := m)
    rfl rfl rfl rfl (by show 8 ≤ 8 + 2 * d; omega) hrn hrd hR0n hR0d hRn (by positivity) bz b1 hP.regs.1 hR' hF'
    brn.le brd.le bR0n.le bR0d.le bRn bPF (by omega) (by omega) (by omega))) fun σ1 ⟨c0, c1, cK, c2K, d1, F1⟩ => ?_
  generalize hK : cmcK (parO d n δ).p (6 * qn (parO d n δ).pF (parO d n δ).R * R0.num * (r0.den : ℤ) * r0.den)
      (2 ^ (parO d n δ).pF * (R0.den : ℤ) * r0.num * r0.num) = K at cK c2K hKb hKC
  -- the start
  have F1' : FrameA (fun y => y = sBadS ∨ 29 < y) (fun j => 8 ≤ j) (fun b _ => 8 ≤ b) σ σ1 :=
    F1.mono (fun y h => Or.inr (by simp only [qX] at h; omega)) (fun j h => by simp only [qX] at h; omega)
      fun _ _ h => h.elim
  refine XVO.seq (XVO.ofX (XV.crossI hL (by omega) (by omega) (by omega) hd
    (by rw [F1'.2.1 sZ (by decide)]; exact bz) (by rw [F1'.2.1 26 (by decide)]; exact b26)
    (by rw [F1'.2.1 27 (by decide)]; exact b27) (by rw [F1'.1 rD (by decide)]; exact b0)
    (by rw [F1'.1 rOne (by decide)]; exact b1) (by omega) hda)) fun σ2 ⟨s33, sB2, a02, az2, d2, F2⟩ => ?_
  have F12 : FrameA (fun y => y = sBadS ∨ 29 < y) (fun j => 8 ≤ j) (fun b _ => 8 ≤ b) σ σ2 :=
    F1'.trans (F2.mono (fun y h => h.elim (fun h => Or.inr (by omega)) Or.inl) (fun j h => by omega)
      fun b _ h => by omega)
  have dat2 : TstDat qX DS muS aS Da Na r0.num r0.den K σ2 := by
    refine ⟨?_, ?_, ?_, ?_, fun i => ?_, fun i j => ?_, ?_⟩
    · rw [F12.1 rD (by decide)]; exact b0
    · rw [F12.1 rOne (by decide)]; exact b1
    · rw [F12.2.1 sZ (by decide)]; exact bz
    · rw [F12.2.1 sDS (by decide)]; exact hDSo
    · rw [F12.2.2.1 aMuS i (fun h => absurd (show 8 ≤ aMuS from h) (by decide))]; exact (hmuS i).2.1
    · rw [F12.2.2.1 aAS _ (fun h => absurd (show 8 ≤ aAS from h) (by decide))]; exact (haS i j).2.1
    · unfold CMDat
      simp only [cmLayQ, qX]
      refine ⟨?_, fun i => ?_, ?_, ?_, ?_, ?_⟩
      · rw [F12.2.2.1 aC 0 (by decide)]; exact hDao
      · rw [F12.2.2.1 aC _ (fun h => absurd (show 8 ≤ aC from h) (by decide)), Nat.add_comm 1]; exact (hNa i).2.1
      · rw [F2.2.1 30 (by decide)]; exact c0
      · rw [F2.2.1 31 (by decide)]; exact c1
      · rw [F2.1 16 (by decide)]; exact cK
      · rw [F2.2.1 32 (by decide)]; exact c2K
  -- the link with BL-O's test
  have hmuQ : ∀ j, ((muS j : ℤ) : ℚ) / (DS : ℚ) = (cfgS n δ r0 R0 a S).μS j := fun j => (hmuS j).2.2
  have haSQ : ∀ i j, ((aS i j : ℤ) : ℚ) / (DS : ℚ) = (cfgS n δ r0 R0 a S).AS i j := fun i j => (haS i j).2.2
  have haQ : ptDN Da Na = (cfgS n δ r0 R0 a S).a := funext fun j => (hNa j).2.2
  have hrQ : ((r0.num : ℤ) : ℚ) / (((r0.den : ℕ) : ℤ) : ℚ) = (cfgS n δ r0 R0 a S).r0 := by
    rw [Int.cast_natCast]; exact Rat.num_div_den r0
  have eT : ∀ y, cmQ (ctxU w n δ r0 R0 a).w.orc (ptDN Da Na) (((r0.num : ℤ) : ℚ) / (((r0.den : ℕ) : ℤ) : ℚ)) K
      (pmap DS muS aS y) = (cfgS n δ r0 R0 a S).T w.orc (cfgS n δ r0 R0 a S).kC 1 y := fun y => by
    rw [hKC]; exact pmap_T (ctxU w n δ r0 R0 a).w.orc _ hDS0 hmuQ haSQ haQ hrQ K y
  -- the turns
  refine XVO.mono (XVO.forN hL (i := 40) (n := rD) (one := rOne) (by omega) (by suomega) (by suomega) (by decide)
    (by decide) d (2 * tstK d + 13) (by omega) (fun t σ' => TstDat qX DS muS aS Da Na r0.num r0.den K σ' ∧
      σ'.arr 12 0 = 2 ∧ (∀ j : Fin d, σ'.arr 12 (1 + (j : ℕ)) = 0) ∧ σ'.sc 33 = -1 ∧ σ'.sc 26 = 1 ∧
      σ'.sc sBadS = ((if ∀ j : Fin d, (j : ℕ) < t →
        ((cfgS n δ r0 R0 a S).T w.orc (cfgS n δ r0 R0 a S).kC 1 (Pi.single j (1 / 2)) = true ∧
          (cfgS n δ r0 R0 a S).T w.orc (cfgS n δ r0 R0 a S).kC 1 (Pi.single j (-1 / 2)) = true)
        then 0 else 1 : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = sBadS ∨ 29 < y) (fun j => 8 ≤ j) (fun b _ => 8 ≤ b) σ σ') σ2 dat2.hd dat2.h1 ?_ ?_)
    le_rfl ?_
  · refine ⟨dat2.frame ((FrameA.refl (fun _ => False) (fun j => j = 40) (fun _ _ => False) σ2).setNat rfl 0)
      (by decide) (by decide) (fun _ => ⟨id, id, id⟩), by rw [Env.setNat_arr]; exact a02,
      fun j => by rw [Env.setNat_arr]; exact az2 j, by rw [Env.setNat_sc]; exact s33, ?_, ?_, ?_,
      F12.setNat (by norm_num) 0⟩
    · rw [Env.setNat_sc, F2.2.1 26 (by decide), F1'.2.1 26 (by decide)]; exact b26
    · rw [Env.setNat_sc, sB2, if_pos (fun j hj => absurd hj (Nat.not_lt_zero _))]; simp
    · rw [Env.setNat_draws, d2, d1]
  · intro t ht σ' ⟨dat', a0', az', s33', s26', fl', dr', F'⟩ h40 hn' h1'
    refine XVO.mono (XVO.crossB hL (by omega) (by omega) (by omega) hd hDS0 bDS bmu baS hdm hDa0 bDa bNa hrn brn
      hrd brd (by omega) (by omega) hda ⟨t, ht⟩ dat' h40 a0' az' s33' s26' fl') le_rfl
      fun σ'' ⟨dat'', a0'', az'', s33'', s26'', fl'', dr'', F''⟩ => ?_
    refine ⟨by rw [F''.1 40 (by decide)]; exact h40, by rw [F''.1 rD (by decide)]; exact hn',
      by rw [F''.1 rOne (by decide)]; exact h1', dat''.frame
        ((FrameA.refl (fun _ => False) (fun j => j = 40) (fun _ _ => False) σ'').setNat rfl _) (by decide)
        (by decide) (fun _ => ⟨id, id, id⟩), by rw [Env.setNat_arr]; exact a0'',
      fun j => by rw [Env.setNat_arr]; exact az'' j, by rw [Env.setNat_sc]; exact s33'',
      by rw [Env.setNat_sc]; exact s26'', ?_, by rw [Env.setNat_draws, dr'', dr'], ?_⟩
    · rw [Env.setNat_sc, fl'']
      congr 1
      refine if_congr ?_ rfl rfl
      rw [eT, eT]
      simp only [Int.cast_one, Int.cast_neg]
      constructor
      · rintro ⟨⟨hP', h1⟩, h2⟩ j hj
        by_cases hjt : (j : ℕ) < t
        · exact hP' j hjt
        · obtain rfl : j = ⟨t, ht⟩ := Fin.ext (by simp only; omega)
          exact ⟨h1, h2⟩
      · intro h
        exact ⟨⟨fun j hj => h j (by omega), (h ⟨t, ht⟩ (by simp)).1⟩, (h ⟨t, ht⟩ (by simp)).2⟩
    · exact (F'.trans (F''.mono (fun y h => h.elim Or.inl fun h => Or.inr (by omega))
        (fun j h => by simp only [nXB] at h; omega) fun _ _ h => h.1)).setNat (by norm_num) _
  · rintro σ' ⟨⟨-, -, -, -, -, fl, dr, F⟩, -⟩
    refine ⟨?_, dr, F⟩
    rw [fl]
    congr 1
    exact if_congr ⟨fun h j => h j j.2, fun h j _ => h j⟩ rfl rfl

end AdversarialBco.Unified.ProgO
