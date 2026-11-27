/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriStage

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the proof of one stage

The bounds of the integer core (`tzDCO_ok`, `tzDCO_Bh_le`, `tzIterO_bound`, `tzSumO_bound`), the coins of the core
(`stSumO_Yc`), the rule of the core `XVO.coreO` (v2.1's `XV.core` with the core step as a contract), its units
`coreKO`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO
open BitRAM BitRAMO

variable {d : ℕ}

/-! ## Bounds of the integer core -/

theorem tzDCO_ok (d ℓ : ℕ) :
    0 ≤ (tzDCO d ℓ).R ∧ (tzDCO d ℓ).R ≤ (tzDCO d ℓ).Bh ∧ 0 < (tzDCO d ℓ).Al ∧ (tzDCO d ℓ).Al ≤ (tzDCO d ℓ).Bh ∧
      0 ≤ (tzDCO d ℓ).PG ∧ (tzDCO d ℓ).PG ≤ (tzDCO d ℓ).Bh := by
  have hLa := triLa_ge d
  have key : ∀ x : ℕ, x ≤ triLa (triSQ d) - 10 + tGT d ℓ →
      (2 : ℤ) ^ x ≤ 161 * 2 ^ (triLa (triSQ d) - 10 + tGT d ℓ) := fun x hx => by
    calc (2 : ℤ) ^ x ≤ 2 ^ (triLa (triSQ d) - 10 + tGT d ℓ) := pow_le_pow_right₀ (by norm_num) hx
      _ ≤ 161 * 2 ^ (triLa (triSQ d) - 10 + tGT d ℓ) := le_mul_of_one_le_left (by positivity) (by norm_num)
  have hG : triBvQ d + triJsTQ d ℓ ≤ tGT d ℓ := by unfold tGT; omega
  simp only [tzDCO]
  refine ⟨by positivity, ?_, by positivity, key _ (by omega), by positivity, key _ (by omega)⟩
  rw [show triLa (triSQ d) - 3 + tGT d ℓ = (triLa (triSQ d) - 10 + tGT d ℓ) + 7 by omega, pow_add, mul_comm]
  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

theorem tzDCO_Bh_le (d ℓ : ℕ) : (tzDCO d ℓ).Bh ≤ 2 ^ (triLa (triSQ d) + tGT d ℓ) := by
  have hLa := triLa_ge d
  show (161 : ℤ) * 2 ^ (triLa (triSQ d) - 10 + tGT d ℓ) ≤ 2 ^ (triLa (triSQ d) + tGT d ℓ)
  have hx : triLa (triSQ d) + tGT d ℓ = 10 + (triLa (triSQ d) - 10 + tGT d ℓ) := by omega
  generalize triLa (triSQ d) - 10 + tGT d ℓ = x at hx ⊢
  rw [hx, pow_add]
  exact mul_le_mul_of_nonneg_right (show (161 : ℤ) ≤ 2 ^ 10 by norm_num) (by positivity)

theorem tzIterO_bound (c : DC) (gv : (Fin d → ℤ) → Fin d → ℤ) (Bb : ℤ) (Y : ℕ → Fin d → ℤ) (hR : 0 ≤ c.R)
    (hRB : c.R ≤ c.Bh) (hAl : 0 < c.Al) (hAB : c.Al ≤ c.Bh) (hPG : 0 ≤ c.PG) (hPGB : c.PG ≤ c.Bh) :
    ∀ t, (∀ i, |(tzIterO c gv Bb Y t).1 i| ≤ c.Bh) ∧ ∀ i l, |(tzIterO c gv Bb Y t).2 i l| ≤ c.Bh
  | 0 => by
    have h0 : 0 ≤ c.Bh := hR.trans hRB
    refine ⟨fun i => by simp [tzIterO, h0], fun i l => ?_⟩
    simp only [tzIterO, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one, abs_of_nonneg hPG]; exact hPGB
    · simp [h0]
  | t + 1 => by
    obtain ⟨h1, h2, -⟩ := tzUpd_bound c (tzIterO c gv Bb Y t) (gv (tzZ (tzIterO c gv Bb Y t) (Y t) c.P2)) (Y t) Bb
      hR hRB hAl hAB
    exact ⟨h1, h2⟩

theorem tzSumO_bound (c : DC) (gv : (Fin d → ℤ) → Fin d → ℤ) (Bb : ℤ) (Y : ℕ → Fin d → ℤ) (hR : 0 ≤ c.R)
    (hRB : c.R ≤ c.Bh) (hAl : 0 < c.Al) (hAB : c.Al ≤ c.Bh) (hPG : 0 ≤ c.PG) (hPGB : c.PG ≤ c.Bh) (N : ℕ) :
    (∀ i, |(tzSumO c gv Bb Y N).1 i| ≤ N * c.Bh) ∧ ∀ i l, |(tzSumO c gv Bb Y N).2 i l| ≤ N * c.Bh := by
  have hb := tzIterO_bound c gv Bb Y hR hRB hAl hAB hPG hPGB
  constructor
  · intro i
    unfold tzSumO
    rw [Prod.fst_sum, Finset.sum_apply]
    calc |∑ t ∈ Finset.range N, (tzIterO c gv Bb Y t).1 i| ≤ ∑ t ∈ Finset.range N, |(tzIterO c gv Bb Y t).1 i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range N, c.Bh := Finset.sum_le_sum fun t _ => (hb t).1 i
      _ = N * c.Bh := by simp
  · intro i l
    unfold tzSumO
    rw [Prod.snd_sum, Matrix.sum_apply]
    calc |∑ t ∈ Finset.range N, (tzIterO c gv Bb Y t).2 i l| ≤
          ∑ t ∈ Finset.range N, |(tzIterO c gv Bb Y t).2 i l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range N, c.Bh := Finset.sum_le_sum fun t _ => (hb t).2 i l
      _ = N * c.Bh := by simp

/-- The core output of a stage on the coins from `c₀` is the sum on v2.1's draws `tzYc` from `c₀`. -/
theorem stSumO_Yc (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ j : ℕ) (P : StZ d)
    (cs : ℕ → Bool) (c0 : ℕ) :
    stSumO orc a r0 R0 ℓ j P (fun k => cs (c0 + k)) =
      tzSumO (tzDCO d ℓ) (gvO orc a r0 R0 ℓ j P) (tBb d) (tzYc cs (triBgQ d) c0) (2 ^ triNeTQ d ℓ) := by
  have hY : tzY d (triBgQ d) (fun k => cs (c0 + k)) = tzYc cs (triBgQ d) c0 :=
    funext fun t => tzY_shift (triBgQ d) c0 t cs _ fun k _ => rfl
  unfold stSumO stSumY
  rw [hY]

/-! ## The core -/

/-- The slots the core writes. -/
abbrev coSO (y : ℕ) : Prop := (oT + 16 ≤ y ∧ y < oT + 35) ∨ oT + 40 ≤ y

/-- The registers the core writes. -/
abbrev coNO (j : ℕ) : Prop := (rT + 3 ≤ j ∧ j < rT + 12) ∨ (rT + 13 ≤ j ∧ j < rT + 24) ∨ rT + 30 ≤ j

/-- The array cells the core writes. -/
abbrev coAO (b _k : ℕ) : Prop := aT + 2 ≤ b

/-- The units of the core with `N` draws, BM-INT in `U` units and the step in `Kst` units. -/
abbrev coreKO (d N U Kst : ℕ) : ℕ :=
  1 + (d * (1 + 6) + 3) + (1 + (d * d * (1 + 6) + 3) + (1 + (d * (1 + 6) + 3)) + (1 + (d * (1 + 6) + 3) +
    (1 + (d * d * (1 + 6) + 3) + (N * (1 + (d * (5 + 6) + 3) + (1 + (d * d * (5 + 6) + 3) +
      (d * (U + 2 + 3) + 3 + Kst)) + 3) + 3))))

set_option maxHeartbeats 4000000 in
/-- **The core of TRI-OGD-O** on the machine: `X̂ := (0, P_G I)`, `Ŝ := 0`, then `N'` times `Ŝ += X̂`, a draw, the core
step; the sum of the iterates `tzSumO` in `aT + 4`, `aT + 5`. -/
theorem XVO.coreO {L : Layout} {w : WorldO d} {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {ℓa ℓ : ℕ} {σ : Env d}
    {xstep : Layout → XCmdO} {KX : KPred} {Ct kt nS nN nA j B E : ℕ} {P : StZ d}
    (hstep : TriStepSpec xstep KX Ct kt nS nN nA) (hX : KXStable KX)
    (hI : InU d n δ r0 R0) (hL : LayOK L d ℓa) (hR : RoomO L nS nN nA)
    (hS : oT + 113 ≤ L.NS) (hN : rT + 30 ≤ L.NN) (hA : aT + 16 ≤ L.NA)
    (hV : TriKV d n δ r0 R0 σ) (hKX : KX d n δ r0 R0 a σ) (hSt : StAtO σ j P) (hB : StBnd P B)
    (hj : j < triMstQ r0 R0) (h1 : σ.nat rT = 1)
    (bBh : (tzDCO d (ellO d n δ r0 R0)).Bh ≤ 2 ^ E)
    (bNB : ((2 ^ triNeTQ d (ellO d n δ r0 R0) : ℕ) : ℤ) * (tzDCO d (ellO d n δ r0 R0)).Bh ≤ 2 ^ E)
    (b4p : 4 * tzP d + 4 ≤ ℓ) (hE : E + 1 < ℓ)
    (hNa : 2 ^ triNeTQ d (ellO d n δ r0 R0) < 2 ^ ℓa) (hBa : 4 * tzP d + 2 < 2 ^ ℓa)
    (hℓt : Ct * (WT d n δ r0 R0 a + B + 1) ^ kt ≤ ℓ) (hℓat : Ct * (WT d n δ r0 R0 a + B + 1) ^ kt < 2 ^ ℓa) :
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xcoreO xstep L) σ
      (coreKO d (2 ^ triNeTQ d (ellO d n δ r0 R0)) (bmUnits (triBgQ d)) (Ct * (WT d n δ r0 R0 a + B + 1) ^ kt))
      (fun σ' =>
        (∀ l : Fin d, σ'.arr (aT + 4) l = (tzSumO (tzDCO d (ellO d n δ r0 R0))
          (gvO w.orc a r0 R0 (ellO d n δ r0 R0) j P) (tBb d) (tzYc w.cs (triBgQ d) σ.draws)
          (2 ^ triNeTQ d (ellO d n δ r0 R0))).1 l) ∧
        (∀ i l : Fin d, σ'.arr (aT + 5) (d * i + l) = (tzSumO (tzDCO d (ellO d n δ r0 R0))
          (gvO w.orc a r0 R0 (ellO d n δ r0 R0) j P) (tBb d) (tzYc w.cs (triBgQ d) σ.draws)
          (2 ^ triNeTQ d (ellO d n δ r0 R0))).2 i l) ∧
        σ'.draws = σ.draws + 2 * triBgQ d * d * 2 ^ triNeTQ d (ellO d n δ r0 R0) ∧
        KX d n δ r0 R0 a σ' ∧ FrameA coSO coNO coAO σ σ') := by
  obtain ⟨hR0, hRB, hAl, hAB, hPG, hPGB⟩ := tzDCO_ok d (ellO d n δ r0 R0)
  have hNA : ∀ k, k < 16 → aT + k < L.NA := fun k h => by omega
  have hNN : ∀ k, k < 30 → rT + k < L.NN := fun k h => by omega
  have hdN : rD < L.NN := by simp only [rD]; omega
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hda : d * d + d < 2 ^ ℓa := asz_lt hL (show aT < L.NA by omega)
  have hcd : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  have hE1 : E < ℓ := by omega
  have hBh0 : 0 ≤ (tzDCO d (ellO d n δ r0 R0)).Bh := hR0.trans hRB
  have bPG : |(tzDCO d (ellO d n δ r0 R0)).PG| ≤ 2 ^ E := by rw [abs_of_nonneg hPG]; exact hPGB.trans bBh
  have zone : ∀ {S N' : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σa σb : Env d}, KX d n δ r0 R0 a σa →
      FrameA S N' Ar σa σb → (∀ y, S y → oT ≤ y) → (∀ j, N' j → rT ≤ j ∧ j < rT + 30) →
      (∀ b k, Ar b k → aT ≤ b ∧ b < aT + 16) → KX d n δ r0 R0 a σb :=
    fun hk F hs hn ha => hX _ _ _ _ _ _ _ _ hk (F.mono hs hn ha)
  obtain ⟨vz, -, -, -, -, -⟩ : σ.sc (oT + 1) = 0 ∧ True ∧ True ∧ True ∧ True ∧ True := ⟨hV.z, trivial, trivial,
    trivial, trivial, trivial⟩
  -- `X̂_μ := 0`
  refine XVO.seq (XVO.ofX (XV.fill hL (z := oT + 1) (t := oT + 40) (s := oT + 1) (aB := aT + 2) (nr := rT + 4)
    (nst := rT) (nk := rT + 5) (nn := rD) (none := rT) (N := d) (st := 1) (E := E) (v := 0) (by omega) (by omega)
    (by omega) vz (hNA 2 (by norm_num)) (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) hdN
    (hNN 0 (by norm_num)) (by simp [rD]) (by omega) (by omega) hV.rd h1 h1 one_pos
    (fun k hk => by rw [one_mul]; exact hcd k hk) (by omega) (by omega) hsa (by rw [vz]; simp) (by simp) hE1))
    fun σ1 ⟨x1, d1, F1⟩ => ?_
  have G1 : FrameA coSO coNO coAO σ σ1 := F1.mono (fun y h => by simp only [coSO]; omega)
    (fun j h => by simp only [coNO]; omega) (fun b k h => by simp only [coAO]; omega)
  have K1 := zone hKX F1 (fun y h => by omega) (fun j h => by omega) (fun b k h => by omega)
  have V1 := hV.frame G1 (fun k hk => by simp only [coSO]; omega) (by simp only [coNO, rD]; omega)
  -- `X̂_T := P_G I`
  refine XVO.seq (XVO.ofX (XV.scalI hL (z := oT + 1) (t := oT + 40) (s := oT + 6) (aB := aT + 3) (nr := rT + 4)
    (n1 := rT) (nd1 := rT + 1) (nk := rT + 5) (nd := rD) (ndd := rT + 25) (none := rT) (E := E)
    (v := (tzDCO d (ellO d n δ r0 R0)).PG) (by omega) (by omega) (by omega) V1.z (hNA 3 (by norm_num))
    (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 1 (by norm_num)) (hNN 5 (by norm_num)) hdN
    (hNN 25 (by norm_num)) (hNN 0 (by norm_num)) (by simp [rD]) (by omega) (by omega) (by omega) (by omega)
    V1.rd V1.rdd (by rw [G1.1 _ (by simp only [coNO]; omega), h1]) (by rw [G1.1 _ (by simp only [coNO]; omega), h1])
    V1.r1 hda V1.pg bPG hE1)) fun σ2 ⟨x2, d2, F2⟩ => ?_
  have G2 : FrameA coSO coNO coAO σ σ2 := G1.trans (F2.mono (fun y h => by simp only [coSO]; omega)
    (fun j h => by simp only [coNO]; omega) (fun b k h => by simp only [coAO]; omega))
  have K2 := zone K1 F2 (fun y h => by omega) (fun j h => by omega) (fun b k h => by omega)
  have V2 := hV.frame G2 (fun k hk => by simp only [coSO]; omega) (by simp only [coNO, rD]; omega)
  -- `Ŝ_μ := 0`
  refine XVO.seq (XVO.ofX (XV.fill hL (z := oT + 1) (t := oT + 40) (s := oT + 1) (aB := aT + 4) (nr := rT + 4)
    (nst := rT) (nk := rT + 5) (nn := rD) (none := rT) (N := d) (st := 1) (E := E) (v := 0) (by omega) (by omega)
    (by omega) V2.z (hNA 4 (by norm_num)) (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) hdN
    (hNN 0 (by norm_num)) (by simp [rD]) (by omega) (by omega) V2.rd
    (by rw [G2.1 _ (by simp only [coNO]; omega), h1]) (by rw [G2.1 _ (by simp only [coNO]; omega), h1]) one_pos
    (fun k hk => by rw [one_mul]; exact hcd k hk) (by omega) (by omega) hsa (by rw [V2.z]; simp) (by simp) hE1))
    fun σ3 ⟨x3, d3, F3⟩ => ?_
  have G3 : FrameA coSO coNO coAO σ σ3 := G2.trans (F3.mono (fun y h => by simp only [coSO]; omega)
    (fun j h => by simp only [coNO]; omega) (fun b k h => by simp only [coAO]; omega))
  have K3 := zone K2 F3 (fun y h => by omega) (fun j h => by omega) (fun b k h => by omega)
  have V3 := hV.frame G3 (fun k hk => by simp only [coSO]; omega) (by simp only [coNO, rD]; omega)
  -- `Ŝ_T := 0`
  refine XVO.seq (XVO.ofX (XV.fill hL (z := oT + 1) (t := oT + 40) (s := oT + 1) (aB := aT + 5) (nr := rT + 4)
    (nst := rT) (nk := rT + 5) (nn := rT + 25) (none := rT) (N := d * d) (st := 1) (E := E) (v := 0) (by omega)
    (by omega) (by omega) V3.z (hNA 5 (by norm_num)) (hNN 4 (by norm_num)) (hNN 0 (by norm_num))
    (hNN 5 (by norm_num)) (hNN 25 (by norm_num)) (hNN 0 (by norm_num)) (by simp) (by omega) (by omega) V3.rdd
    (by rw [G3.1 _ (by simp only [coNO]; omega), h1]) (by rw [G3.1 _ (by simp only [coNO]; omega), h1]) one_pos
    (fun k hk => by rw [one_mul]; exact cell_sq hk) (by omega) (by omega) hsa (by rw [V3.z]; simp) (by simp) hE1))
    fun σ4 ⟨x4, d4, F4⟩ => ?_
  have G4 : FrameA coSO coNO coAO σ σ4 := G3.trans (F4.mono (fun y h => by simp only [coSO]; omega)
    (fun j h => by simp only [coNO]; omega) (fun b k h => by simp only [coAO]; omega))
  have K4 := zone K3 F4 (fun y h => by omega) (fun j h => by omega) (fun b k h => by omega)
  -- the draws
  set c := tzDCO d (ellO d n δ r0 R0) with hc
  set gv := gvO w.orc a r0 R0 (ellO d n δ r0 R0) j P with hgv
  set Y := tzYc (d := d) w.cs (triBgQ d) σ.draws with hY
  set N := 2 ^ triNeTQ d (ellO d n δ r0 R0) with hNdef
  have x2' : ∀ i l : Fin d, σ4.arr (aT + 3) (d * i + l) = (tzIterO c gv (tBb d) Y 0).2 i l := fun i l => by
    rw [F4.2.2.1 _ _ (by omega), F3.2.2.1 _ _ (by omega), x2]; rfl
  have x1' : ∀ l : Fin d, σ4.arr (aT + 2) l = (tzIterO c gv (tBb d) Y 0).1 l := fun l => by
    rw [F4.2.2.1 _ _ (by omega), F3.2.2.1 _ _ (by omega), F2.2.2.1 _ _ (by omega)]
    have := x1 l l.2; rw [one_mul] at this; rw [this]; rfl
  have s3' : ∀ l : Fin d, σ4.arr (aT + 4) l = (tzSumO c gv (tBb d) Y 0).1 l := fun l => by
    rw [F4.2.2.1 _ _ (by omega)]
    have := x3 l l.2; rw [one_mul] at this; rw [this]; simp [tzSumO]
  have s4' : ∀ i l : Fin d, σ4.arr (aT + 5) (d * i + l) = (tzSumO c gv (tBb d) Y 0).2 i l := fun i l => by
    have := x4 _ (cell_dil i l); rw [one_mul] at this; rw [this]; simp [tzSumO]
  let J : ℕ → Env d → Prop := fun t σ' =>
    (∀ l : Fin d, σ'.arr (aT + 2) l = (tzIterO c gv (tBb d) Y t).1 l) ∧
    (∀ i l : Fin d, σ'.arr (aT + 3) (d * i + l) = (tzIterO c gv (tBb d) Y t).2 i l) ∧
    (∀ l : Fin d, σ'.arr (aT + 4) l = (tzSumO c gv (tBb d) Y t).1 l) ∧
    (∀ i l : Fin d, σ'.arr (aT + 5) (d * i + l) = (tzSumO c gv (tBb d) Y t).2 i l) ∧
    σ'.draws = σ.draws + 2 * triBgQ d * d * t ∧ KX d n δ r0 R0 a σ' ∧ FrameA coSO coNO coAO σ σ'
  refine XVO.mono (XVO.forN (L := L) (XO := ctxU w n δ r0 R0 a) (ℓ := ℓ) (i := rT + 11) (n := rT + 24) (one := rT)
    (body := xcoreBodyO xstep L) hL (hNN 11 (by norm_num)) (hNN 24 (by norm_num)) (hNN 0 (by norm_num))
    (by omega) (by omega) N _ hNa J σ4 (by rw [G4.1 _ (by simp only [coNO]; omega), hV.rN])
    (by rw [G4.1 _ (by simp only [coNO]; omega), h1])
    ⟨fun l => by rw [Env.setNat_arr, x1' l], fun i l => by rw [Env.setNat_arr, x2' i l],
      fun l => by rw [Env.setNat_arr, s3' l], fun i l => by rw [Env.setNat_arr, s4' i l],
      by rw [Env.setNat_draws, d4, d3, d2, d1]; ring,
      zone K4 ((FrameA.refl (fun _ => False) (fun j => j = rT + 11) (fun _ _ => False) σ4).setNat rfl 0)
        (fun y h => h.elim) (fun j h => by omega) (fun b k h => h.elim),
      G4.setNat (by simp only [coNO]; omega) _⟩ ?_) le_rfl ?_
  · intro t ht σ' ⟨jx1, jx2, js1, js2, jd, jK, jG⟩ hkt hkn hk1
    obtain ⟨bI1, bI2⟩ := tzIterO_bound c gv (tBb d) Y hR0 hRB hAl hAB hPG hPGB t
    obtain ⟨bS1, bS2⟩ := tzSumO_bound c gv (tBb d) Y hR0 hRB hAl hAB hPG hPGB t
    have htN : (t : ℤ) * c.Bh ≤ 2 ^ E := by
      have : (t : ℤ) ≤ (N : ℕ) := by exact_mod_cast ht.le
      exact (mul_le_mul_of_nonneg_right this hBh0).trans bNB
    have Vj := hV.frame jG (fun k hk => by simp only [coSO]; omega) (by simp only [coNO, rD]; omega)
    -- `Ŝ_μ += X̂_μ`
    refine XVO.seq (XVO.ofX (XV.acc hL (z := oT + 1) (t := oT + 40) (aB := aT + 4) (aX := aT + 2) (nr := rT + 4)
      (nst := rT) (nk := rT + 5) (nn := rD) (none := rT) (N := d) (E := E)
      (U := vext (tzSumO c gv (tBb d) Y t).1) (V := vext (tzIterO c gv (tBb d) Y t).1)
      (by omega) (by omega) Vj.z (hNA 4 (by norm_num)) (hNA 2 (by norm_num)) (hNN 4 (by norm_num))
      (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) hdN (hNN 0 (by norm_num)) (by simp [rD]) (by omega) (by omega)
      Vj.rd hk1 hk1 hcd (by omega) (vec_cells js1) (vec_cells jx1)
      (fun k hk => by rw [vext_lt _ hk]; exact (bS1 _).trans htN)
      (fun k hk => by rw [vext_lt _ hk]; exact (bI1 _).trans bBh) hE)) fun σa ⟨xa, da, Fa⟩ => ?_
    -- `Ŝ_T += X̂_T`
    refine XVO.seq (XVO.ofX (XV.acc hL (z := oT + 1) (t := oT + 40) (aB := aT + 5) (aX := aT + 3) (nr := rT + 4)
      (nst := rT) (nk := rT + 5) (nn := rT + 25) (none := rT) (N := d * d) (E := E)
      (U := tmext (tzSumO c gv (tBb d) Y t).2) (V := tmext (tzIterO c gv (tBb d) Y t).2)
      (by omega) (by omega) (by rw [Fa.2.1 _ (by omega), Vj.z]) (hNA 5 (by norm_num)) (hNA 3 (by norm_num))
      (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) (hNN 25 (by norm_num))
      (hNN 0 (by norm_num)) (by simp) (by omega) (by omega) (by rw [Fa.1 _ (by omega), Vj.rdd])
      (by rw [Fa.1 _ (by omega), hk1]) (by rw [Fa.1 _ (by omega), hk1]) (fun k hk => cell_sq hk) (by omega)
      (mat_cells fun i l => by rw [Fa.2.2.1 _ _ (by omega)]; exact js2 i l)
      (mat_cells fun i l => by rw [Fa.2.2.1 _ _ (by omega)]; exact jx2 i l)
      (fun k _ => tmext_abs_le (by positivity) (fun i l => (bS2 i l).trans htN) k)
      (fun k _ => tmext_abs_le (by positivity) (fun i l => (bI2 i l).trans bBh) k) hE)) fun σb ⟨xb, db, Fb⟩ => ?_
    have Gb : FrameA coSO coNO coAO σ σb := (jG.trans (Fa.mono (fun y h => by simp only [coSO]; omega)
      (fun j h => by simp only [coNO]; omega) (fun b k h => by simp only [coAO]; omega))).trans
      (Fb.mono (fun y h => by simp only [coSO]; omega) (fun j h => by simp only [coNO]; omega)
        (fun b k h => by simp only [coAO]; omega))
    have Kb := zone (zone jK Fa (fun y h => by omega) (fun j h => by omega) (fun b k h => by omega)) Fb
      (fun y h => by omega) (fun j h => by omega) (fun b k h => by omega)
    have Vb := hV.frame Gb (fun k hk => by simp only [coSO]; omega) (by simp only [coNO, rD]; omega)
    -- the draw
    refine XVO.seq (XVO.ofX (XV.draw hL (o := oT + 70) (on := rT + 12) (aY := aT + 6) (ni := rT + 7) (nd := rD)
      (none := rT) (B := triBgQ d) (by omega) (by omega) (by unfold triBgQ triKgQ; omega) Vb.rB hBa
      (by unfold tzP at b4p; omega) (hNA 6 (by norm_num)) (hNN 7 (by norm_num)) hdN (hNN 0 (by norm_num))
      (by simp [rD]) (by omega) (by omega) (by simp [rD]) (by omega) Vb.rd
      (by rw [Gb.1 _ (by simp only [coNO]; omega), h1]) hda
      (fun U W hU _ => XV.abs_int_lt (lt_of_le_of_lt (BLM.gsSpec_abs_le _ U W hU).1
        (pow_lt_pow_right₀ (by norm_num) (by unfold tzP at b4p; omega)))))) fun σc ⟨yc, dc, Fc⟩ => ?_
    have Gc : FrameA coSO coNO coAO σ σc := Gb.trans (Fc.mono (fun y h => by simp only [coSO]; omega)
      (fun j h => by simp only [coNO]; omega) (fun b k h => by simp only [coAO]; omega))
    have Kc := zone Kb Fc (fun y h => by omega) (fun j h => by omega) (fun b k h => by omega)
    have Vc := hV.frame Gc (fun k hk => by simp only [coSO]; omega) (by simp only [coNO, rD]; omega)
    have Sc : StAtO σc j P := by
      obtain ⟨e1, e2, e3, e4⟩ := hSt
      exact ⟨fun l => by rw [Gc.2.2.1 _ _ (by simp only [coAO]; omega), e1],
        fun i l => by rw [Gc.2.2.1 _ _ (by simp only [coAO]; omega), e2],
        by rw [Gc.2.1 _ (by simp only [coSO]; omega), e3], by rw [Gc.2.1 _ (by simp only [coSO]; omega), e4]⟩
    have dσc : σc.draws = σ.draws + 2 * triBgQ d * d * t + 2 * triBgQ d * d := by rw [dc, db, da, jd]
    -- the step
    refine XVO.mono (hstep d L w n δ r0 R0 a ℓa ℓ σc j B P (tzIterO c gv (tBb d) Y t) (Y t) hI hL hR Vc Kc Sc hB hj
      (by rw [Gc.1 _ (by simp only [coNO]; omega), h1])
      (fun l => by rw [Fc.2.2.1 _ _ (by omega), Fb.2.2.1 _ _ (by omega), Fa.2.2.1 _ _ (by omega), jx1 l])
      (fun i l => by rw [Fc.2.2.1 _ _ (by omega), Fb.2.2.1 _ _ (by omega), Fa.2.2.1 _ _ (by omega), jx2 i l])
      (fun l => by rw [yc l, db, da, jd]; rfl) bI1 bI2 (fun l => gsAt_abs_le _ _ _ _) hℓt hℓat) le_rfl ?_
    rintro σd ⟨xd1, xd2, Kd, dd, Fd⟩
    have Gd : FrameA coSO coNO coAO σ σd := Gc.trans (Fd.mono (fun y h => by simp only [stpS, coSO] at h ⊢; omega)
      (fun j h => by simp only [stpN, coNO] at h ⊢; omega) (fun b k h => by simp only [stpA, coAO] at h ⊢; omega))
    have hsucc : tzSumO c gv (tBb d) Y (t + 1) = tzSumO c gv (tBb d) Y t + tzIterO c gv (tBb d) Y t :=
      Finset.sum_range_succ _ _
    refine ⟨by rw [Fd.1 _ (by simp only [stpN]; omega), Fc.1 _ (by omega), Fb.1 _ (by omega), Fa.1 _ (by omega),
      hkt], by rw [Gd.1 _ (by simp only [coNO]; omega), hV.rN], by rw [Gd.1 _ (by simp only [coNO]; omega), h1],
      fun l => by rw [Env.setNat_arr, xd1 l]; rfl, fun i l => by rw [Env.setNat_arr, xd2 i l]; rfl,
      fun l => ?_, fun i l => ?_, by rw [Env.setNat_draws, dd, dσc]; ring,
      zone Kd ((FrameA.refl (fun _ => False) (fun j => j = rT + 11) (fun _ _ => False) σd).setNat rfl _)
        (fun y h => h.elim) (fun j h => by omega) (fun b k h => h.elim),
      Gd.setNat (by simp only [coNO]; omega) _⟩
    · rw [Env.setNat_arr, Fd.2.2.1 _ _ (by simp only [stpA]; omega), Fc.2.2.1 _ _ (by omega),
        Fb.2.2.1 _ _ (by omega), xa l l.2, vext_lt _ l.2, vext_lt _ l.2, hsucc]
      simp
    · rw [Env.setNat_arr, Fd.2.2.1 _ _ (by simp only [stpA]; omega), Fc.2.2.1 _ _ (by omega),
        xb _ (cell_dil i l), tmext_cell, tmext_cell, hsucc]
      simp
  · rintro σ' ⟨⟨_, _, js1, js2, jd, jK, jG⟩, -, -, -⟩
    exact ⟨js1, js2, jd, jK, jG⟩


/-! ## The stage -/

/-- The units of a stage: the core, two constants, the composition, the doubling of `2^{j+1}`. -/
abbrev stageKO (d N U Kst : ℕ) : ℕ := coreKO d N U Kst + (1 + (1 + (stageCK d + 1)))

/-- The constant of the units of a stage. -/
def triCS (Ct _kt Ce _ke : ℕ) : ℕ := 256 * (Ce + Ct + 1) ^ 3

/-- The degree of the units of a stage. -/
def triKS (kt ke : ℕ) : ℕ := 3 * (ke + kt + 1)

theorem stageKO_le {d N U Kst Z : ℕ} (hZ : 1 ≤ Z) (hd : d ≤ Z) (hN : N ≤ Z) (hU : U ≤ Z) (hK : Kst ≤ Z) :
    stageKO d N U Kst ≤ 256 * Z ^ 3 := by
  have h1 : stageKO d N U Kst ≤ stageKO Z Z Z Z := by
    simp only [stageKO, coreKO, stageCK, matmulK, mmRowK]
    gcongr
  refine h1.trans ?_
  have a1 : Z ≤ Z ^ 3 := Nat.le_self_pow (by norm_num) Z
  have a2 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ (by norm_num)
  have a0 : 1 ≤ Z ^ 3 := Nat.one_le_pow _ _ hZ
  simp only [stageKO, coreKO, stageCK, matmulK, mmRowK]
  ring_nf
  omega

/-- The arithmetic of a stage: its units, and a margin `16 (V + X + K_st)` below the bound, `V = W + B + 1`,
`X = C_e (W + 1)^{k_e}`. -/
theorem stage_arith (W B Ce ke Ct kt d N U : ℕ) (hd : d ≤ Ce * (W + 1) ^ ke) (hN : N ≤ Ce * (W + 1) ^ ke)
    (hU : U ≤ Ce * (W + 1) ^ ke) :
    stageKO d N U (Ct * (W + B + 1) ^ kt) ≤ triCS Ct kt Ce ke * (W + B + 1) ^ triKS kt ke ∧
      16 * (W + B + 1 + Ce * (W + 1) ^ ke + Ct * (W + B + 1) ^ kt) <
        triCS Ct kt Ce ke * (W + B + 1) ^ triKS kt ke := by
  have hV1 : 1 ≤ W + B + 1 := by omega
  have hX : Ce * (W + 1) ^ ke ≤ (Ce + Ct + 1) * (W + B + 1) ^ (ke + kt + 1) :=
    Nat.mul_le_mul (by omega) ((Nat.pow_le_pow_left (by omega) ke).trans (Nat.pow_le_pow_right hV1 (by omega)))
  have hK : Ct * (W + B + 1) ^ kt ≤ (Ce + Ct + 1) * (W + B + 1) ^ (ke + kt + 1) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hV1 (by omega))
  have hVZ : W + B + 1 ≤ (Ce + Ct + 1) * (W + B + 1) ^ (ke + kt + 1) := by
    calc W + B + 1 = 1 * (W + B + 1) ^ 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hV1 (by omega))
  have hCs : triCS Ct kt Ce ke * (W + B + 1) ^ triKS kt ke =
      256 * ((Ce + Ct + 1) * (W + B + 1) ^ (ke + kt + 1)) ^ 3 := by
    simp only [triCS, triKS]; rw [mul_pow, ← pow_mul]; ring
  rw [hCs]
  generalize (Ce + Ct + 1) * (W + B + 1) ^ (ke + kt + 1) = Z at hX hK hVZ ⊢
  generalize Ce * (W + 1) ^ ke = X at hX hd hN hU ⊢
  generalize Ct * (W + B + 1) ^ kt = Kst at hK ⊢
  generalize W + B + 1 = V at hVZ hV1 ⊢
  have hZ1 : 1 ≤ Z := hV1.trans hVZ
  have a1 : Z ≤ Z ^ 3 := Nat.le_self_pow (by norm_num) Z
  have a0 : 1 ≤ Z ^ 3 := Nat.one_le_pow _ _ hZ1
  exact ⟨stageKO_le hZ1 (hd.trans hX) (hN.trans hX) (hU.trans hX) hK, by omega⟩

set_option maxHeartbeats 8000000 in
/-- **One stage of TRI-OGD-O** (`TriStageSpec`) for `xstageO xstep`, from the core step `TriStepSpec`, the exponent
bounds `TriExpO` and `KXStable`. -/
theorem triStageSpec_of {xstep : Layout → XCmdO} {KX : KPred} {Ct kt Ce ke nS nN nA : ℕ}
    (hstep : TriStepSpec xstep KX Ct kt nS nN nA) (hexp : TriExpO Ce ke) (hX : KXStable KX)
    (hnS : oT + 113 ≤ nS) (hnN : rT + 30 ≤ nN) (hnA : aT + 16 ≤ nA) :
    TriStageSpec (xstageO xstep) (KEv KX) (triCS Ct kt Ce ke) (triKS kt ke) nS nN nA := by
  intro d L w n δ r0 R0 a ℓa ℓ σ j B P hI hL hR hKE hSt hB hj h1 h27 h28 hℓ hℓa
  obtain ⟨hV, hKX⟩ := hKE
  obtain ⟨eX1, eX2, eX3⟩ := hexp d n δ r0 R0 a hI
  have hm : triMstQ r0 R0 ≤ WT d n δ r0 R0 a := mst_le_wU a hI
  obtain ⟨hU, hT⟩ := stage_arith (WT d n δ r0 R0 a) B Ce ke Ct kt d (2 ^ triNeTQ d (ellO d n δ r0 R0))
    (bmUnits (triBgQ d)) (by omega) eX2 eX3
  have hS' : oT + 113 ≤ L.NS := hnS.trans hR.1
  have hN' : rT + 30 ≤ L.NN := hnN.trans hR.2.1
  have hA' : aT + 16 ≤ L.NA := hnA.trans hR.2.2
  obtain ⟨e1, e2, e3, e4⟩ := hSt
  have hGE : triLa (triSQ d) + tGcT d (ellO d n δ r0 R0) ≤ Ce * (WT d n δ r0 R0 a + 1) ^ ke := by omega
  have bBh : (tzDCO d (ellO d n δ r0 R0)).Bh ≤ 2 ^ (Ce * (WT d n δ r0 R0 a + 1) ^ ke) :=
    (tzDCO_Bh_le d _).trans (pow_le_pow_right₀ (by norm_num) (by unfold tGcT at hGE; omega))
  have bNB : ((2 ^ triNeTQ d (ellO d n δ r0 R0) : ℕ) : ℤ) * (tzDCO d (ellO d n δ r0 R0)).Bh ≤
      2 ^ (Ce * (WT d n δ r0 R0 a + 1) ^ ke) := by
    push_cast
    calc (2 : ℤ) ^ triNeTQ d (ellO d n δ r0 R0) * (tzDCO d (ellO d n δ r0 R0)).Bh ≤
          2 ^ triNeTQ d (ellO d n δ r0 R0) * 2 ^ (triLa (triSQ d) + tGT d (ellO d n δ r0 R0)) :=
          mul_le_mul_of_nonneg_left (tzDCO_Bh_le d _) (by positivity)
      _ = 2 ^ (triLa (triSQ d) + tGcT d (ellO d n δ r0 R0)) := by
          rw [← pow_add]; congr 1; unfold tGcT; omega
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hGE
  obtain ⟨hR0, hRB, hAl, hAB, hPG, hPGB⟩ := tzDCO_ok d (ellO d n δ r0 R0)
  refine XVO.mono ?_ hU (fun _ h => h)
  -- the core
  refine XVO.seq (XVO.coreO (E := Ce * (WT d n δ r0 R0 a + 1) ^ ke) hstep hX hI hL hR hS' hN' hA' hV hKX
    ⟨e1, e2, e3, e4⟩ hB hj h1 bBh bNB (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun σ1 ⟨s1, s2, d1, K1, F1⟩ => ?_
  have V1 := hV.frame F1 (fun k hk => by simp only [coSO]; omega) (by simp only [coNO, rD]; omega)
  -- `2^e := 1`, `Q := 0`
  refine XVO.seq (XVO.ofX (XV.constI hL (x := oT + 14) (by omega) 1
    (by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)))) fun σ2 e2' => ?_
  refine XVO.seq (XVO.ofX (XV.constI hL (x := oT + 15) (by omega) 0 (by simp))) fun σ3 e3' => ?_
  have sc3 : ∀ y, y ≠ oT + 14 → y ≠ oT + 15 → σ3.sc y = σ1.sc y := fun y h14 h15 => by
    rw [e3', e2']; simp [h14, h15]
  have nat3 : σ3.nat = σ1.nat := by rw [e3', e2']; rfl
  have arr3 : σ3.arr = σ1.arr := by rw [e3', e2']; rfl
  have dr3 : σ3.draws = σ1.draws := by rw [e3', e2']; rfl
  have F13 : ∀ (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop), S (oT + 14) → S (oT + 15) → FrameA S N Ar σ1 σ3 :=
    fun S N Ar h14 h15 => by rw [e3', e2']; exact ((FrameA.refl S N Ar σ1).setSc h14 _).setSc h15 _
  have bS := tzSumO_bound (tzDCO d (ellO d n δ r0 R0)) (gvO w.orc a r0 R0 (ellO d n δ r0 R0) j P) (tBb d)
    (tzYc w.cs (triBgQ d) σ.draws) hR0 hRB hAl hAB hPG hPGB (2 ^ triNeTQ d (ellO d n δ r0 R0))
  have pE : ∀ x, x ≤ B + Ce * (WT d n δ r0 R0 a + 1) ^ ke → (2 : ℤ) ^ x ≤ 2 ^ (B + Ce * (WT d n δ r0 R0 a + 1) ^ ke) :=
    fun x hx => pow_le_pow_right₀ (by norm_num) hx
  -- the composition
  refine XVO.seq (XVO.ofX (XV.stageC hL (o := oT) (r := rT) (a := aT) (nd := rD) (Gc := tGcT d (ellO d n δ r0 R0))
    (e := 0) (E := B + Ce * (WT d n δ r0 R0 a + 1) ^ ke) (P := P)
    (S := tzSumO (tzDCO d (ellO d n δ r0 R0)) (gvO w.orc a r0 R0 (ellO d n δ r0 R0) j P) (tBb d)
      (tzYc w.cs (triBgQ d) σ.draws) (2 ^ triNeTQ d (ellO d n δ r0 R0))) (Q := 0)
    (by omega) (by omega) hA' (by simp only [rD, rT]; omega) (by rw [nat3]; exact V1.rd)
    (by rw [nat3, F1.1 _ (by simp only [coNO]; omega)]; exact h1) (by rw [nat3]; exact V1.rdd)
    (by rw [sc3 _ (by omega) (by omega)]; exact V1.z) (by rw [sc3 _ (by omega) (by omega)]; exact V1.o)
    (by rw [sc3 _ (by omega) (by omega), F1.2.1 _ (by simp only [coSO]; omega)]; exact e3)
    (by rw [e3', e2']; simp) (by rw [e3']; simp)
    (by rw [sc3 _ (by omega) (by omega)]; exact V1.gc)
    (fun l => by rw [arr3, F1.2.2.1 _ _ (by simp only [coAO]; omega)]; exact e1 l)
    (fun i l => by rw [arr3, F1.2.2.1 _ _ (by simp only [coAO]; omega)]; exact e2 i l)
    (fun l => by rw [arr3]; exact s1 l) (fun i l => by rw [arr3]; exact s2 i l)
    (fun l => (hB.2.2.1 l).trans (pE _ (by omega))) (fun i l => (hB.2.2.2 i l).trans (pE _ (by omega)))
    (fun l => (bS.1 l).trans (bNB.trans (pE _ (by omega))))
    (fun i l => (bS.2 i l).trans (bNB.trans (pE _ (by omega))))
    (by rw [abs_of_pos hB.1]; exact hB.2.1.trans (pE _ (by omega))) (Nat.zero_le _) (by simp)
    (by omega) (by omega))) fun σ4 ⟨m4, t4, D4, _, _, dr4, F4⟩ => ?_
  -- `2^{j+1} := 2^{j+2}`
  have e36 : σ4.sc (oT + 36) = ((2 ^ (j + 1) : ℤ) : ℝ) := by
    rw [F4.2.1 _ (by simp only [stcS]; omega), sc3 _ (by omega) (by omega), F1.2.1 _ (by simp only [coSO]; omega)]
    exact e4
  have b1 : |(2 : ℤ) ^ (j + 1)| < 2 ^ ℓ := by
    rw [abs_of_pos (by positivity)]; exact pow_lt_pow_right₀ (by norm_num) (by omega)
  refine XVO.mono (XVO.ofX (XV.addI hL (x := oT + 36) (a := oT + 36) (b := oT + 36) (u := 2 ^ (j + 1))
    (v := 2 ^ (j + 1)) (by omega) (by omega) (by omega) e36 e36 b1 b1
    (by rw [← two_mul, ← pow_succ', abs_of_pos (by positivity)]; exact pow_lt_pow_right₀ (by norm_num) (by omega))))
    le_rfl fun σ5 e5 => ?_
  have F45 : ∀ (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop), S (oT + 36) → FrameA S N Ar σ4 σ5 :=
    fun S N Ar h36 => by rw [e5]; exact (FrameA.refl S N Ar σ4).setSc h36 _
  have G : FrameA (fun y => coSO y ∨ stcS oT y ∨ y = oT + 36) (fun j => coNO j ∨ stcN rT j)
      (fun b k => coAO b k ∨ stcA d aT b k) σ σ5 :=
    (((F1.mono (fun y h => Or.inl h) (fun j h => Or.inl h) (fun b k h => Or.inl h)).trans
      (F13 (fun y => coSO y ∨ stcS oT y ∨ y = oT + 36) (fun j => coNO j ∨ stcN rT j)
        (fun b k => coAO b k ∨ stcA d aT b k) (Or.inr (Or.inl (Or.inr (Or.inl rfl))))
        (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl))))))).trans
      (F4.mono (fun y h => Or.inr (Or.inl h)) (fun j h => Or.inr h) (fun b k h => Or.inr h))).trans
      (F45 _ _ _ (Or.inr (Or.inr rfl)))
  have Z15 : FrameA (fun y => oT ≤ y) (fun j => rT ≤ j ∧ j < rT + 30) (fun b _ => aT ≤ b ∧ b < aT + 16) σ1 σ5 :=
    ((F13 _ _ _ (by omega) (by omega)).trans (F4.mono (fun y h => by simp only [stcS] at h; omega)
      (fun j h => by simp only [stcN] at h; omega) (fun b k h => by simp only [stcA] at h; omega))).trans
      (F45 _ _ _ (by omega))
  have hY := stSumO_Yc w.orc a r0 R0 (ellO d n δ r0 R0) j P w.cs σ.draws
  refine ⟨⟨hV.frame G (fun k hk => by simp only [coSO, stcS]; omega) (by simp only [coNO, stcN, rD]; omega),
    hX _ _ _ _ _ _ σ1 σ5 K1 Z15⟩, ⟨fun l => ?_, fun i l => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hY, e5, Env.setSc_arr]; exact m4 l
  · rw [hY, e5, Env.setSc_arr]; exact t4 i l
  · rw [hY, e5, Env.setSc_sc, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ oT = oT + 36 by omega))]; exact D4
  · rw [e5, Env.setSc_sc, ite_eq_left_of_eq_true _ _ (eq_self _)]; push_cast; ring
  · rw [G.1 _ (by simp only [coNO, stcN]; omega)]; exact h1
  · rw [G.1 _ (by simp only [coNO, stcN]; omega)]; exact h27
  · rw [G.1 _ (by simp only [coNO, stcN]; omega)]; exact h28
  · rw [e5, Env.setSc_draws, dr4, dr3, d1]; unfold triLTQ; ring
  · exact G.mono (fun y h => by simp only [coSO, stcS, TriS, sDS, oT] at h ⊢; omega)
      (fun j h => by simp only [coNO, stcN, TriN, rT] at h ⊢; omega)
      (fun b k h => by simp only [coAO, stcA, ATri, aT] at h ⊢; omega)

end AdversarialBco.Unified.ProgO.TriO
