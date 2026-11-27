/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriStage
public import AdversarialBco.Unified.ProgOSetupCoins

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the output

`xoutO L`: the last stage `P` from the stage cells into BL's cells (`D` into `sDS`, `μ̂` into `aMuS`, `T̂` into `aAS`,
v2.1's `xmapE` through `base`), then `LposO = m_st · (N' · (2 d B_g))` into `sLp`, from the registers `rT + 28`,
`rT + 24`, `rT + 12` and `rD`. `triOutSpec_of : TriExpO Ce ke → TriOutSpec xoutO (KEv KX) (triCO Ce) (ke + 2) ..`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO
open BitRAM BitRAMO

variable {d : ℕ}

/-- **The output of TRI-OGD-O**: `D`, `μ̂`, `T̂` into `sDS`, `aMuS`, `aAS`, then `LposO` into `sLp`. -/
def xoutO (L : Layout) : XCmdO :=
  .seq (.base (toX (VL.sop2 L .add sDS oT (oT + 1))))
  (.seq (.base (.prim (.frag (.nconst (rT + 4) 0))))
  (.seq (.base (xmapE L (oT + 1) (oT + 40) (.arr aT (rT + 4)) aMuS (rT + 4) rT (rT + 5) rD rT))
  (.seq (.base (.prim (.frag (.nconst (rT + 4) 0))))
  (.seq (.base (xmapE L (oT + 1) (oT + 40) (.arr (aT + 1) (rT + 4)) aAS (rT + 4) rT (rT + 5) (rT + 25) rT))
  (.seq (.base (toX (VL.ncast L (oT + 40) (rT + 28))))
  (.seq (.base (toX (VL.ncast L (oT + 41) (rT + 24))))
  (.seq (.base (toX (VL.ncast L (oT + 42) (rT + 12))))
  (.seq (.base (toX (VL.ncast L (oT + 43) rD)))
  (.seq (.base (toX (VL.sop2 L .mul (oT + 44) (oT + 40) (oT + 41))))
  (.seq (.base (toX (VL.sop2 L .mul (oT + 44) (oT + 44) (oT + 43))))
  (.seq (.base (toX (VL.sop2 L .mul (oT + 44) (oT + 44) (oT + 42))))
  (.base (toX (VL.sop2 L .add sLp (oT + 44) (oT + 44)))))))))))))))

/-- The units of the output. -/
abbrev outKO (d : ℕ) : ℕ :=
  1 + (1 + (d * (2 + 6) + 3 + (1 + (d * d * (2 + 6) + 3 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))

/-- The constant of the units of the output. -/
def triCO (Ce : ℕ) : ℕ := 2048 * (Ce + 1)

theorem out_arith (W B Ce ke d : ℕ) (hd : d ≤ W) :
    outKO d ≤ triCO Ce * (W + B + 1) ^ (ke + 2) ∧
      1200 * (W + 1) + B + Ce * (W + 1) ^ ke + 2 < triCO Ce * (W + B + 1) ^ (ke + 2) := by
  have hV : 1 ≤ W + B + 1 := by omega
  have hZ2 : (W + B + 1) ^ 2 ≤ (W + B + 1) ^ (ke + 2) := Nat.pow_le_pow_right hV (by omega)
  have hZ1 : W + B + 1 ≤ (W + B + 1) ^ 2 := by nlinarith
  have hX : Ce * (W + 1) ^ ke ≤ Ce * (W + B + 1) ^ (ke + 2) :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) ke).trans (Nat.pow_le_pow_right hV (by omega)))
  have hdd : d * d ≤ (W + B + 1) ^ 2 := by nlinarith
  have hC : triCO Ce * (W + B + 1) ^ (ke + 2) = 2048 * (Ce * (W + B + 1) ^ (ke + 2)) + 2048 * (W + B + 1) ^ (ke + 2) :=
    by simp only [triCO]; ring
  rw [hC]
  simp only [outKO]
  generalize (W + B + 1) ^ (ke + 2) = Z at hZ2 hX ⊢
  generalize (W + B + 1) ^ 2 = Y at hZ1 hZ2 hdd
  generalize Ce * (W + 1) ^ ke = X at hX ⊢
  generalize Ce * Z = CZ at hX ⊢
  generalize d * d = dd at hdd ⊢
  constructor <;> omega

theorem sc_of_setSc_ne {σ σ' : Env d} {x y : ℕ} {v : ℝ} (e : σ' = σ.setSc x v) (h : y ≠ x) : σ'.sc y = σ.sc y := by
  rw [e]; simp [h]

theorem sc_of_setSc_eq {σ σ' : Env d} {x : ℕ} {v : ℝ} (e : σ' = σ.setSc x v) : σ'.sc x = v := by
  rw [e]; simp

theorem frame_of_setSc {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} {x : ℕ} {v : ℝ} (e : σ' = σ.setSc x v)
    (hx : S x) : FrameA S N Ar σ σ' := by
  rw [e]; exact (FrameA.refl S N Ar σ).setSc hx v

set_option maxHeartbeats 8000000 in
/-- **The output of TRI-OGD-O** meets `TriOutSpec` for the constants `KEv KX`. -/
theorem triOutSpec_of {KX : KPred} {Ce ke nS nN nA : ℕ} (hexp : TriExpO Ce ke) (hnS : oT + 45 ≤ nS)
    (hnN : rT + 29 ≤ nN) (hnA : aT + 2 ≤ nA) : TriOutSpec xoutO (KEv KX) (triCO Ce) (ke + 2) nS nN nA := by
  intro d L w n δ r0 R0 a ℓa ℓ σ B P hI hL hR hKE hSt hB h1 h28 hℓ hℓa
  obtain ⟨hV, -⟩ := hKE
  obtain ⟨e1, e2, e3, -⟩ := hSt
  obtain ⟨eX1, eX2, -⟩ := hexp d n δ r0 R0 a hI
  have hdW : d ≤ WT d n δ r0 R0 a := by simp only [WT, wU]; omega
  obtain ⟨hU, hM⟩ := out_arith (WT d n δ r0 R0 a) B Ce ke d hdW
  have hLp : LposO d n δ r0 R0 ≤ 2 ^ (1200 * (WT d n δ r0 R0 a + 1)) := LposO_le a hI
  have hmW : triMstQ r0 R0 ≤ WT d n δ r0 R0 a := mst_le_wU a hI
  have hS' : oT + 45 ≤ L.NS := hnS.trans hR.1
  have hN' : rT + 29 ≤ L.NN := hnN.trans hR.2.1
  have hA' : aT + 2 ≤ L.NA := hnA.trans hR.2.2
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hda : d * d + d < 2 ^ ℓa := asz_lt hL (show aT < L.NA by omega)
  have hd1 : 1 ≤ d := hI.hd
  have hg1 : 1 ≤ triBgQ d := by unfold triBgQ triKgQ; omega
  have hgp : triBgQ d ≤ tzP d := by unfold tzP gsm_prec; omega
  have hBl : B < ℓ := by omega
  have hpB : ∀ x : ℤ, |x| ≤ 2 ^ B → |x| < 2 ^ ℓ := fun x hx =>
    lt_of_le_of_lt hx (pow_lt_pow_right₀ (by norm_num) hBl)
  have hpL : ∀ x : ℕ, x ≤ LposO d n δ r0 R0 → |(x : ℤ)| < 2 ^ ℓ := fun x hx => by
    have h1' : x < 2 ^ ℓ := lt_of_le_of_lt (hx.trans hLp) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    rw [Nat.abs_cast]
    exact_mod_cast h1'
  have bD : |P.D| ≤ 2 ^ B := by rw [abs_of_pos hB.1]; exact hB.2.1
  -- the precise frame of the block
  let So : ℕ → Prop := fun y => y = sDS ∨ oT + 40 ≤ y ∨ y = sLp
  let No : ℕ → Prop := fun j => j = rT + 4 ∨ j = rT + 5
  let Ao : ℕ → ℕ → Prop := fun b c => (b = aMuS ∧ c < d) ∨ (b = aAS ∧ c < d * d)
  refine XVO.mono ?_ hU (fun _ h => h)
  -- `sDS := D`
  refine XVO.seq (XVO.ofX (XV.addI hL (x := sDS) (a := oT) (b := oT + 1) (u := P.D) (v := 0)
    (by simp only [sDS]; omega) (by omega) (by omega) e3 (by rw [hV.z]; simp) (hpB _ bD) (by simp)
    (by rw [add_zero]; exact hpB _ bD))) fun σ1 x1 => ?_
  have G1 : FrameA So No Ao σ σ1 := by rw [x1]; exact (FrameA.refl So No Ao σ).setSc (Or.inl rfl) _
  have v1 : σ1.sc sDS = P.D := by rw [x1, Env.setSc_sc, ite_eq_left_of_eq_true _ _ (eq_self _), add_zero]
  -- `μ̂` into `aMuS`
  refine XVO.seq (XVO.ofX (XV.nconst hL (i := rT + 4) (by omega) 0 (by positivity))) fun σ2 x2 => ?_
  have G2 : FrameA So No Ao σ σ2 := by rw [x2]; exact G1.setNat (Or.inl rfl) _
  refine XVO.seq (XVO.ofX (XV.mapE hL (z := oT + 1) (t := oT + 40) (e := .arr aT (rT + 4)) (aB := aMuS)
    (nr := rT + 4) (nst := rT) (nk := rT + 5) (nn := rD) (none := rT) (E := B) (N := d) (base := 0) (st := 1)
    (F := vext P.mu) (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega)
    (by rw [G2.2.1 _ (by simp only [So, sDS, sLp, oT]; omega)]; exact hV.z) (by simp only [aMuS]; omega)
    (by omega) (by omega) (by omega) (by simp only [rD]; omega) (by omega)
    (by simp only [rT, rD]; decide) (by omega) (by omega)
    (by rw [G2.1 _ (by simp only [No, rD]; omega)]; exact hV.rd)
    (by rw [G2.1 _ (by simp only [No]; omega)]; exact h1) (by rw [x2, Env.setNat_nat, ite_eq_left_of_eq_true _ _ (eq_self _)])
    (by rw [G2.1 _ (by simp only [No]; omega)]; exact h1) one_pos
    (fun k hk => by unfold asz; omega) (by omega) (by omega) hsa (by simp only [IE.top]; omega)
    (fun k hk σ' F' _ _ hr' => ?_))) fun σ3 ⟨m3, _, d3, F3⟩ => ?_
  · have hk'' : σ'.nat (rT + 4) = k := by rw [hr']; ring
    have vp : σ'.arr aT k = vext P.mu k := by
      rw [F'.2.2.1 aT k (by simp only [aMuS, aT]; omega), G2.2.2.1 _ _ (by simp only [Ao, aMuS, aAS, aT]; omega)]
      exact vec_cells e1 k hk
    exact ⟨⟨by rw [hk'']; unfold asz; omega, _, by rw [hk'', vp], by rw [vext_lt _ hk]; exact hB.2.2.1 _⟩,
      by simp only [IE.eval, hk'', vp]⟩
  have G3 : FrameA So No Ao σ σ3 := G2.trans (F3.mono (fun y h => Or.inr (Or.inl h))
    (fun j h => by simp only [No]; omega) (fun b c h => Or.inl ⟨h.1, by omega⟩))
  -- `T̂` into `aAS`
  refine XVO.seq (XVO.ofX (XV.nconst hL (i := rT + 4) (by omega) 0 (by positivity))) fun σ4 x4 => ?_
  have G4 : FrameA So No Ao σ σ4 := by rw [x4]; exact G3.setNat (Or.inl rfl) _
  refine XVO.seq (XVO.ofX (XV.mapE hL (z := oT + 1) (t := oT + 40) (e := .arr (aT + 1) (rT + 4)) (aB := aAS)
    (nr := rT + 4) (nst := rT) (nk := rT + 5) (nn := rT + 25) (none := rT) (E := B) (N := d * d) (base := 0)
    (st := 1) (F := tmext P.T) (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega)
    (by rw [G4.2.1 _ (by simp only [So, sDS, sLp, oT]; omega)]; exact hV.z) (by simp only [aAS]; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [rT]; decide) (by omega) (by omega)
    (by rw [G4.1 _ (by simp only [No]; omega)]; exact hV.rdd)
    (by rw [G4.1 _ (by simp only [No]; omega)]; exact h1) (by rw [x4, Env.setNat_nat, ite_eq_left_of_eq_true _ _ (eq_self _)])
    (by rw [G4.1 _ (by simp only [No]; omega)]; exact h1) one_pos
    (fun k hk => by unfold asz; omega) (by omega) (by omega) hsa (by simp only [IE.top]; omega)
    (fun k hk σ' F' _ _ hr' => ?_))) fun σ5 ⟨m5, _, d5, F5⟩ => ?_
  · have hk'' : σ'.nat (rT + 4) = k := by rw [hr']; ring
    have vp : σ'.arr (aT + 1) k = tmext P.T k := by
      rw [F'.2.2.1 (aT + 1) k (by simp only [aAS, aT]; omega),
        G4.2.2.1 _ _ (by simp only [Ao, aMuS, aAS, aT]; omega)]
      exact mat_cells e2 k hk
    exact ⟨⟨by rw [hk'']; unfold asz; omega, _, by rw [hk'', vp], tmext_abs_le (by positivity) hB.2.2.2 k⟩,
      by simp only [IE.eval, hk'', vp]⟩
  have G5 : FrameA So No Ao σ σ5 := G4.trans (F5.mono (fun y h => Or.inr (Or.inl h))
    (fun j h => by simp only [No]; omega) (fun b c h => Or.inr ⟨h.1, by omega⟩))
  -- `LposO` into `sLp`
  have hS2 : 175 ≤ L.NS := hS'
  have H5 : FrameA (fun y => oT + 40 ≤ y ∨ y = sLp) No Ao σ1 σ5 :=
    ((((by rw [x2]; exact (FrameA.refl _ No Ao σ1).setNat (Or.inl rfl) _ :
      FrameA (fun y => oT + 40 ≤ y ∨ y = sLp) No Ao σ1 σ2).trans (F3.mono (fun y h => Or.inl h)
      (fun j h => by simp only [No]; omega) (fun b c h => Or.inl ⟨h.1, by omega⟩))).trans
      (by rw [x4]; exact (FrameA.refl _ No Ao σ3).setNat (Or.inl rfl) _)).trans
      (F5.mono (fun y h => Or.inl h) (fun j h => by simp only [No]; omega) (fun b c h => Or.inr ⟨h.1, by omega⟩)))
  have r28 : σ5.nat (rT + 28) = triMstQ r0 R0 := by rw [G5.1 _ (by simp only [No]; omega)]; exact h28
  have r24 : σ5.nat (rT + 24) = 2 ^ triNeTQ d (ellO d n δ r0 R0) := by
    rw [G5.1 _ (by simp only [No]; omega)]; exact hV.rN
  have r12 : σ5.nat (rT + 12) = triBgQ d := by rw [G5.1 _ (by simp only [No]; omega)]; exact hV.rB
  have r0' : σ5.nat rD = d := by rw [G5.1 _ (by simp only [No, rD]; omega)]; exact hV.rd
  have hmpos : 0 < triMstQ r0 R0 := by unfold triMstQ; omega
  have hL1 : triMstQ r0 R0 * 2 ^ triNeTQ d (ellO d n δ r0 R0) ≤ LposO d n δ r0 R0 := by
    unfold LposO triLTQ
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos (by norm_num) hd1) hg1))
  have hL4 : 2 * (triMstQ r0 R0 * 2 ^ triNeTQ d (ellO d n δ r0 R0) * d * triBgQ d) = LposO d n δ r0 R0 := by
    unfold LposO triLTQ; ring
  have hL3 : triMstQ r0 R0 * 2 ^ triNeTQ d (ellO d n δ r0 R0) * d * triBgQ d ≤ LposO d n δ r0 R0 := by omega
  have hL2 : triMstQ r0 R0 * 2 ^ triNeTQ d (ellO d n δ r0 R0) * d ≤ LposO d n δ r0 R0 :=
    le_trans (Nat.le_mul_of_pos_right _ hg1) hL3
  have hm0 : triMstQ r0 R0 ≤ LposO d n δ r0 R0 := le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hL1
  have hN0 : 2 ^ triNeTQ d (ellO d n δ r0 R0) ≤ LposO d n δ r0 R0 := le_trans (Nat.le_mul_of_pos_left _ hmpos) hL1
  have hg0 : triBgQ d ≤ LposO d n δ r0 R0 :=
    le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hmpos (Nat.two_pow_pos _)) hd1)) hL3
  have hd0 : d ≤ LposO d n δ r0 R0 :=
    le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos hmpos (Nat.two_pow_pos _))) hL2
  refine XVO.seq (XVO.ofX (XV.ncastI hL (x := oT + 40) (i := rT + 28) (by omega) (by omega)
    (by rw [r28]; omega))) fun σ6 x6 => ?_
  refine XVO.seq (XVO.ofX (XV.ncastI hL (x := oT + 41) (i := rT + 24) (by omega) (by omega)
    (by rw [x6, Env.setSc_nat, r24]; omega))) fun σ7 x7 => ?_
  refine XVO.seq (XVO.ofX (XV.ncastI hL (x := oT + 42) (i := rT + 12) (by omega) (by omega)
    (by rw [x7, Env.setSc_nat, x6, Env.setSc_nat, r12]; omega))) fun σ8 x8 => ?_
  refine XVO.seq (XVO.ofX (XV.ncastI hL (x := oT + 43) (i := rD) (by omega) (by simp only [rD]; omega)
    (by rw [x8, Env.setSc_nat, x7, Env.setSc_nat, x6, Env.setSc_nat, r0']; omega))) fun σ9 x9 => ?_
  have n9 : σ9.nat = σ5.nat := by rw [x9, x8, x7, x6]; rfl
  have v40 : σ9.sc (oT + 40) = ((triMstQ r0 R0 : ℕ) : ℤ) := by
    rw [sc_of_setSc_ne x9 (show oT + 40 ≠ oT + 43 by omega), sc_of_setSc_ne x8 (show oT + 40 ≠ oT + 42 by omega),
      sc_of_setSc_ne x7 (show oT + 40 ≠ oT + 41 by omega), sc_of_setSc_eq x6, r28]
  have v41 : σ9.sc (oT + 41) = ((2 ^ triNeTQ d (ellO d n δ r0 R0) : ℕ) : ℤ) := by
    rw [sc_of_setSc_ne x9 (show oT + 41 ≠ oT + 43 by omega), sc_of_setSc_ne x8 (show oT + 41 ≠ oT + 42 by omega),
      sc_of_setSc_eq x7, x6, Env.setSc_nat, r24]
  have v42 : σ9.sc (oT + 42) = ((triBgQ d : ℕ) : ℤ) := by
    rw [sc_of_setSc_ne x9 (show oT + 42 ≠ oT + 43 by omega), sc_of_setSc_eq x8, x7, Env.setSc_nat, x6,
      Env.setSc_nat, r12]
  have v43 : σ9.sc (oT + 43) = ((d : ℕ) : ℤ) := by
    rw [sc_of_setSc_eq x9, x8, Env.setSc_nat, x7, Env.setSc_nat, x6, Env.setSc_nat, r0']
  refine XVO.seq (XVO.ofX (XV.mulI hL (x := oT + 44) (a := oT + 40) (b := oT + 41)
    (u := ((triMstQ r0 R0 : ℕ) : ℤ)) (v := ((2 ^ triNeTQ d (ellO d n δ r0 R0) : ℕ) : ℤ)) (by omega) (by omega)
    (by omega) v40 v41 (hpL _ hm0) (hpL _ hN0) (by rw [← Nat.cast_mul]; exact hpL _ hL1))) fun σa xa => ?_
  refine XVO.seq (XVO.ofX (XV.mulI hL (x := oT + 44) (a := oT + 44) (b := oT + 43)
    (u := ((triMstQ r0 R0 * 2 ^ triNeTQ d (ellO d n δ r0 R0) : ℕ) : ℤ)) (v := ((d : ℕ) : ℤ)) (by omega)
    (by omega) (by omega) (by rw [sc_of_setSc_eq xa, Nat.cast_mul])
    ((sc_of_setSc_ne xa (show oT + 43 ≠ oT + 44 by omega)).trans v43) (hpL _ hL1) (hpL _ hd0)
    (by rw [← Nat.cast_mul]; exact hpL _ hL2))) fun σb xb => ?_
  refine XVO.seq (XVO.ofX (XV.mulI hL (x := oT + 44) (a := oT + 44) (b := oT + 42)
    (u := ((triMstQ r0 R0 * 2 ^ triNeTQ d (ellO d n δ r0 R0) * d : ℕ) : ℤ)) (v := ((triBgQ d : ℕ) : ℤ))
    (by omega) (by omega) (by omega) (by rw [sc_of_setSc_eq xb]; push_cast; ring)
    ((sc_of_setSc_ne xb (show oT + 42 ≠ oT + 44 by omega)).trans
      ((sc_of_setSc_ne xa (show oT + 42 ≠ oT + 44 by omega)).trans v42))
    (hpL _ hL2) (hpL _ hg0) (by rw [← Nat.cast_mul]; exact hpL _ hL3))) fun σc xc => ?_
  refine XVO.mono (XVO.ofX (XV.addI hL (x := sLp) (a := oT + 44) (b := oT + 44)
    (u := ((triMstQ r0 R0 * 2 ^ triNeTQ d (ellO d n δ r0 R0) * d * triBgQ d : ℕ) : ℤ))
    (v := ((triMstQ r0 R0 * 2 ^ triNeTQ d (ellO d n δ r0 R0) * d * triBgQ d : ℕ) : ℤ))
    (by simp only [sLp]; omega) (by omega) (by omega) (by rw [sc_of_setSc_eq xc]; push_cast; ring)
    (by rw [sc_of_setSc_eq xc]; push_cast; ring) (hpL _ hL3) (hpL _ hL3)
    (by rw [← Nat.cast_add, ← two_mul, hL4]; exact hpL _ le_rfl))) le_rfl fun σd xd => ?_
  have Ff : FrameA (fun y => oT + 40 ≤ y ∨ y = sLp) (fun _ => False) (fun _ _ => False) σ5 σd :=
    ((((((((frame_of_setSc x6 (Or.inl (by omega))).trans (frame_of_setSc x7 (Or.inl (by omega)))).trans
      (frame_of_setSc x8 (Or.inl (by omega)))).trans (frame_of_setSc x9 (Or.inl (by omega)))).trans
      (frame_of_setSc xa (Or.inl (by omega)))).trans (frame_of_setSc xb (Or.inl (by omega)))).trans
      (frame_of_setSc xc (Or.inl (by omega)))).trans (frame_of_setSc xd (Or.inr rfl)))
  have Ff' : FrameA (fun y => oT + 40 ≤ y ∨ y = sLp) No Ao σ5 σd :=
    Ff.mono (fun y h => h) (fun j h => h.elim) (fun b c h => h.elim)
  have Gf : FrameA So No Ao σ σd := G5.trans (Ff'.mono (fun y h => Or.inr h) (fun j h => h) (fun b c h => h))
  refine ⟨?_, fun l => ?_, fun i l => ?_, ?_, ?_, ?_⟩
  · rw [(H5.trans Ff').2.1 _ (by simp only [sDS, sLp, oT]; omega)]; exact v1
  · rw [Ff.2.2.1 _ _ not_false, F5.2.2.1 _ _ (by simp only [aMuS, aAS]; omega), x4,
      Env.setNat_arr]
    have := m3 l l.2
    rw [zero_add, one_mul, vext_lt _ l.2] at this
    exact this
  · rw [Ff.2.2.1 _ _ not_false]
    have := m5 _ (cell_dil i l)
    rw [zero_add, one_mul, tmext_cell] at this
    exact this
  · rw [sc_of_setSc_eq xd, ← hL4]; push_cast; ring
  · rw [xd, Env.setSc_draws, xc, Env.setSc_draws, xb, Env.setSc_draws, xa, Env.setSc_draws, x9, Env.setSc_draws,
      x8, Env.setSc_draws, x7, Env.setSc_draws, x6, Env.setSc_draws, d5, x4, Env.setNat_draws, d3, x2,
      Env.setNat_draws, x1, Env.setSc_draws]
  · exact Gf.mono (fun y h => by simp only [So, TriS, sDS, sLp, oT] at h ⊢; omega)
      (fun j h => by simp only [No, TriN, rT] at h ⊢; omega)
      (fun b c h => by simp only [Ao, ATri] at h ⊢; omega)

end AdversarialBco.Unified.ProgO.TriO
