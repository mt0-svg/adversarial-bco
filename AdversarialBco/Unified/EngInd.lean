/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngRec

@[expose] public section

/-!
# Step 1 of SHADOW for BL-O's record: the induction `IND(t)`

Bit/BLEngine.lean's `eps_facts`, `track_init`, `modeW_zero`, `refYW_eq`, `cY_coupled`, `inv_zero`, `inv_succ`, `ind`
for BL-O's record `recO` (Unified/AsmRec.lean) at `k = k_δ`, with piece C (`RoundCO`, Unified/EngDefs.lean) as a
hypothesis:

* the epoch start: `ε ≤ ε' ≤ 1/2` and `Track` between BL's and P°'s initial states (`eps_factsK`, `track_initK`,
  Theorem BUD at `k`), and BL-O's first mode is `run` on `Case` (`modeO_zero`: the cross check passes by `crossOKO`
  in the good position of radius `R ≤ R'`);
* the round: P°'s observation is the record's `refYO` at P°'s state (`refYO_eq`), so the record's advice is the
  checked advice `advC` of piece C (`adv_eq`); when the round does not decouple, P°'s observation is BL-O's exact
  observation with the noise (`cY_coupledO`, the algebra `y_alg'`);
* `inv_succO`: `RCHypO` from `Case`, `Ω_ref`, `E_bits` and `NoClip`, then `RoundCO`; `indO : RoundCO → IndO`.
-/

open MeasureTheory

namespace AdversarialBco.Unified.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK budO)
open AdversarialBco.Bit.BLP (Par St Mode init refX refPt cV cM opN)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.Poly.Conj1 (fL)
open Matrix

variable {d : ℕ}

/-! ## The epoch start -/

theorem deltaO_lt_one (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : deltaO d n k < 1 :=
  (BudK.deltaO_le d n k hd hn).trans_lt (Bit.Asm.deltaBL_lt_one hd hn)

/-- Lemma ENC on `ε` at `k`: `0 < ε ≤ ε' ≤ 1/2` and `ε' - ε ≤ w_ε`. -/
theorem eps_factsK {d n k : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCaseK d n k) (hbud : BudOK d n k) :
    0 < (poK d n k).eps ∧ (poK d n k).eps ≤ ((parK d n k).eps : ℝ) ∧ ((parK d n k).eps : ℝ) ≤ 1 / 2 ∧
      ((parK d n k).eps : ℝ) - (poK d n k).eps ≤ BudK.we d n k := by
  have H := rowHyp_of d n (deltaO d n k) hd hn (deltaO_pos d n k hd hn) (deltaO_lt_one d n k hd hn)
    (hc.trans (by norm_num))
  have h0 : 0 < (poK d n k).eps := eps_pos_of_rows H
  have h1 := hbud.enc.eps_le
  have h2 := hbud.enc.eps_rel
  have htp0 : 0 ≤ BudK.tp d n k := by unfold BudK.tp; positivity
  have htp1 : BudK.tp d n k ≤ 1 := by
    unfold BudK.tp; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hc' : (poK d n k).eps ≤ 1 / 4 := hc
  unfold BudK.eps at h1 h2
  unfold BudK.we BudK.eps
  generalize ((parK d n k).eps : ℝ) = e' at *
  generalize (poK d n k).eps = e at *
  generalize BudK.tp d n k = tp at *
  refine ⟨h0, h1, ?_, ?_⟩ <;> nlinarith

/-- `TrackK` at the epoch start (Lemma ENC: `A_0`, `B_0`). -/
theorem track_initK {d n k : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCaseK d n k) (hbud : BudOK d n k) :
    TrackK d n k (init (parK d n k) d) (df2Init (poK d n k) d) 0 := by
  have H := rowHyp_of d n (deltaO d n k) hd hn (deltaO_pos d n k hd hn) (deltaO_lt_one d n k hd hn)
    (hc.trans (by norm_num))
  have hLe : 0 < (poK d n k).Le := by have := H.L504; unfold poK; linarith
  have hs : 0 < (poK d n k).sig2 := by
    unfold poK; rw [H.sig2]; apply div_pos one_pos; unfold poK at hLe; linarith
  set s := (poK d n k).sig2 with hs_def
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq2 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have htp0 : 0 ≤ BudK.tp d n k := by unfold BudK.tp; positivity
  have hha : BudK.hTr d n k 0 = BudK.ha d n k := by unfold BudK.hTr; simp
  have hha' : BudK.ha d n k = BudK.tp d n k * Real.sqrt (8 * BudK.Le d n k) + BudK.tp d n k +
      BudK.tp d n k / 16 := by
    unfold BudK.ha; ring
  have hcM : ∀ c : ℚ, cM (c • (1 : Matrix (Fin d) (Fin d) ℚ)) = (c : ℝ) • 1 := by
    intro c; ext i j
    simp only [cM, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]; split_ifs <;> simp
  have hop : ∀ c : ℝ, opN (c • (1 : Matrix (Fin d) (Fin d) ℝ)) ≤ |c| := Bit.BLP.EngL.opN_smul_one d
  have hone : ∀ c : ℝ, (1 : Matrix (Fin d) (Fin d) ℝ) + (c - 1) • 1 = c • 1 := by
    intro c; rw [sub_smul, one_smul]; abel
  have hcV0 : cV (0 : Fin d → ℚ) = 0 := by funext i; simp [cV]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; simp [cV, init, df2Init]
  · show s • (1 : Matrix (Fin d) (Fin d) ℝ) = (Real.sqrt s • 1) * (Real.sqrt s • 1)ᵀ
    rw [Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul_comm, one_mul, hsq2]
  · show s⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) * s • 1 = 1
    rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hs.ne', one_smul]
  · refine ⟨(((parK d n k).A0 : ℝ) / Real.sqrt s - 1) • 1, ?_, ?_⟩
    · show cM ((parK d n k).A0 • 1) = _ * (Real.sqrt s • 1)
      rw [hcM, hone, smul_mul_smul_comm, one_mul, div_mul_cancel₀ _ hsq.ne']
    · refine (hop _).trans ?_
      rw [hha, hha']
      have := hbud.enc.A0
      linarith
  · refine ⟨(((parK d n k).B0 : ℝ) * Real.sqrt s - 1) • 1, ?_, ?_⟩
    · show cM ((parK d n k).B0 • 1) = _ * (s⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) * (Real.sqrt s • 1))
      rw [hcM, hone, smul_mul_smul_comm, one_mul, smul_mul_smul_comm, one_mul]
      congr 1
      field_simp
      rw [Real.sq_sqrt hs.le]
    · refine (hop _).trans ?_
      rw [hha, hha']
      have := hbud.enc.B0
      have h8 : 0 ≤ BudK.tp d n k * Real.sqrt (8 * BudK.Le d n k) := by positivity
      linarith
  · simp [oNorm, hcV0, init, df2Init]
  · simp [init, df2Init]
  · simp [oNorm, hcV0, init, df2Init]
  · simp [init, df2Init]

/-- The frame of BL-O's configuration on an input of `TheoremUnified`. -/
theorem frameW {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool}
    (hI : InpU n δ r0 R0 a K orc) (w : BitRAMO.WorldO d) : FrameO K orc (cfgW d n δ r0 R0 a w) :=
  ⟨hI.convex, hI.compact.isClosed, hI.hr0, hI.hrR, hI.ball_in, hI.ball_out, hI.orc⟩

/-- A good position of `PgGood` is a good position of BL-O's configuration. -/
theorem goodPos_of_pg {K : Set (E d)} {c : CfgO d} {R : ℝ} (h : PgGood d K R (some c.S)) : GoodPos K c R := by
  obtain ⟨P, hP, -, h1, h2, -⟩ := h
  obtain rfl := Option.some_inj.1 hP
  exact ⟨h1, h2⟩

/-- **BL-O starts in mode `run`** in a good position of radius `1 ≤ R ≤ R'` when `ε' ≤ 1/2`. -/
theorem modeO_zero {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool}
    (hI : InpU n δ r0 R0 a K orc) (w : BitRAMO.WorldO d) (hw : w.orc = orc)
    (hq : PgGood d K (poK d n (kDel δ)).R (some (cfgW d n δ r0 R0 a w).S)) (hR1 : 1 ≤ (poK d n (kDel δ)).R)
    (hR : (poK d n (kDel δ)).R ≤ ((parK d n (kDel δ)).R : ℝ)) (heps : (parO d n δ).eps ≤ 1 / 2) :
    modeO d n δ r0 R0 a w 0 = .run (init (parO d n δ) d) := by
  subst hw
  have hx : crossOK w.orc (cfgW d n δ r0 R0 a w) :=
    crossOKO d K w.orc _ _ (frameW hI w) (goodPos_of_pg hq) hR1 hR
  show mode0O w.orc (cfgW d n δ r0 R0 a w) = _
  unfold mode0O
  rw [if_neg (show ¬ (1 / 2 < (cfgW d n δ r0 R0 a w).par.eps) from not_lt.2 heps), if_pos hx]
  rfl

/-! ## The round -/

/-- The algebra of the coupled observation with the shift `(m, r)` named. -/
theorem y_alg' {pto pt' F0 F1 nz Z e e' m r : ℝ} (hp : pto ≠ 0) (hr : r = pt' / pto)
    (hm : m = (pt' / pto - 1) * nz + (pt' * F1 - pto * F0 + 4 * (pt' - 1) / e' - 4 * (pto - 1) / e) / pto) :
    pto * (F0 / 2 + (nz + (m + r * Z / 2)) / 2) + 2 * (pto - 1) / e =
      pt' * (F1 + nz + Z / 2) / 2 + 2 * (pt' - 1) / e' := by
  subst hr hm
  field_simp
  ring

section Rec

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
  {orc : (Fin d → ℚ) → ℕ → Bool}

set_option hygiene false in
local notation "BB" => recO n δ r0 R0 a orc h hI.convex
set_option hygiene false in
local notation "WE" => extO n δ r0 R0 a h
set_option hygiene false in
local notation "WW" => envWorld orc coin loss noise ω.1
set_option hygiene false in
local notation "CC" => cfgW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)
set_option hygiene false in
local notation "DB" => dBL d n δ

/-- `0 < ε < 1` at P°'s parameters in the case `ε ≤ 1/4`. -/
theorem eps01 (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ) :
    0 < (df2oPar d n (dBL d n δ)).eps ∧ (df2oPar d n (dBL d n δ)).eps < 1 := by
  have H := rowHyp_of d n (dBL d n δ) hI.hd hI.hn (deltaO_pos d n _ hI.hd hI.hn)
    (deltaO_lt_one d n _ hI.hd hI.hn) (hc.trans (by norm_num))
  have hc' : (df2oPar d n (dBL d n δ)).eps ≤ 1 / 4 := hc
  exact ⟨eps_pos_of_rows H, by linarith⟩

/-- P°'s observation of round `s` of the epoch is the record's `refYO` at P°'s state. -/
theorem refYO_eq (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case DB ω) {a0 s : ℕ} (ht : a0 + s < n) {so : Df2St d}
    (hso : ((BB).ctx DB a0 ω).st ((BB).path DB a0 ω) s = so) (hmo : (BB).mode DB (a0 + s) ω = .run so) :
    refYO n δ r0 R0 a orc h hI.convex (a0 + s) ω so = ((BB).ctx DB a0 ω).Y ((BB).path DB a0 ω) s := by
  obtain ⟨heps0, heps1⟩ := eps01 hI hc
  rw [RunW.ctx_Y _ hq ht hso, hmo]
  obtain ⟨hrp, hint⟩ := RunW.refPlay_run _ hI.convex hq heps0 heps1 hmo
  rw [hrp] at hint
  have e : refYO n δ r0 R0 a orc h hI.convex (a0 + s) ω so =
      Bit.BLP.EngL.ptE (kTh n DB K ((BB).pos ω)) (df2oPar d n DB).eps
          (WithLp.toLp 2 (so.mu + (1 - (df2oPar d n DB).lam) • (so.A *ᵥ (WE).xi (a0 + s) ω))) *
        ((if a0 + s < n then fL K (BB).F.L (a0 + s) ((BB).F.lam (a0 + s) ω) else 0)
            (pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (WithLp.toLp 2
              ((Bit.BLP.EngL.ptE (kTh n DB K ((BB).pos ω)) (df2oPar d n DB).eps
                (WithLp.toLp 2 (so.mu + (1 - (df2oPar d n DB).lam) • (so.A *ᵥ (WE).xi (a0 + s) ω))))⁻¹ •
                (so.mu + (1 - (df2oPar d n DB).lam) • (so.A *ᵥ (WE).xi (a0 + s) ω))))) +
          (WE).nz (a0 + s) ω + (BB).zeta (a0 + s) ω (.run so)) / 2 +
      2 * (Bit.BLP.EngL.ptE (kTh n DB K ((BB).pos ω)) (df2oPar d n DB).eps
          (WithLp.toLp 2 (so.mu + (1 - (df2oPar d n DB).lam) • (so.A *ᵥ (WE).xi (a0 + s) ω))) - 1) /
        (df2oPar d n DB).eps := rfl
  rw [e, if_pos ht, WithLp.toLp_smul, fL_interior hint]
  have hl : (BB).F.L (a0 + s) ((BB).F.lam (a0 + s) ω) = (BB).loss ω (a0 + s) := rfl
  rw [hl]
  ring

/-- When round `t = a0 + s` does not decouple, P°'s observation is BL-O's exact observation with the noise. -/
theorem cY_coupledO (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case DB ω) {a0 s : ℕ} (ht : a0 + s < n) {so : Df2St d} {st : St d}
    (hso : ((BB).ctx DB a0 ω).st ((BB).path DB a0 ω) s = so) (hmo : (BB).mode DB (a0 + s) ω = .run so)
    (hW : modeO d n δ r0 R0 a WW (a0 + s) = .run st) (hD : ¬ (BB).D DB (a0 + s) ω) :
    ((BB).ctx DB a0 ω).Y ((BB).path DB a0 ω) s =
      (ptO orc CC (XO CC st (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1) : ℝ) *
        ((BB).loss ω (a0 + s) (xO orc CC st (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1) + (WE).nz (a0 + s) ω +
          (WE).zz (a0 + s) ω 0 / 2) / 2 +
      2 * ((ptO orc CC (XO CC st (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1) : ℝ) - 1) / ((CC).par.eps : ℝ) := by
  obtain ⟨heps0, heps1⟩ := eps01 hI hc
  have hD' : (BB).zeta (a0 + s) ω ((BB).mode DB (a0 + s) ω) =
      ((BB).shR DB (a0 + s) ω).1 + ((BB).shR DB (a0 + s) ω).2 * (WE).zz (a0 + s) ω 0 / 2 := not_not.mp hD
  rw [RunW.ctx_Y _ hq ht hso, hD']
  obtain ⟨hrp, hint⟩ := RunW.refPlay_run _ hI.convex hq heps0 heps1 hmo
  rw [hrp] at hint
  set X : Fin d → ℝ := so.mu + (1 - (df2oPar d n DB).lam) • (so.A *ᵥ (WE).xi (a0 + s) ω) with hX
  set PTO := Bit.BLP.EngL.ptE (kTh n DB K ((BB).pos ω)) (df2oPar d n DB).eps (WithLp.toLp 2 X) with hPTO
  set PT1 : ℝ := (ptO orc CC (XO CC st (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1) : ℝ) with hPT1
  have hp0 : 0 < PTO := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hpl : playO d n δ r0 R0 a WW (a0 + s) =
      playPtO orc CC (.run st) (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1 := by
    unfold playO
    rw [hW]
    rfl
  refine y_alg' hp0.ne' ?_ ?_
  · show (shO n δ r0 R0 a orc h hI.convex (a0 + s) ω ((BB).mode DB (a0 + s) ω)).2 = _
    rw [hmo]
    unfold shO
    rw [if_pos ht, hW]
    all_goals rfl
  · have e1 : ((BB).shR DB (a0 + s) ω).1 = (PT1 / PTO - 1) * (WE).nz (a0 + s) ω +
        (PT1 * (BB).F.L (a0 + s) ((BB).F.lam (a0 + s) ω) (toE (playO d n δ r0 R0 a WW (a0 + s))) -
          PTO * (if a0 + s < n then fL K (BB).F.L (a0 + s) ((BB).F.lam (a0 + s) ω) else 0)
            (pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (WithLp.toLp 2 (PTO⁻¹ • X))) +
          4 * (PT1 - 1) / ((CC).par.eps : ℝ) - 4 * (PTO - 1) / (df2oPar d n DB).eps) / PTO := by
      show (shO n δ r0 R0 a orc h hI.convex (a0 + s) ω ((BB).mode DB (a0 + s) ω)).1 = _
      rw [hmo]
      unfold shO
      rw [if_pos ht, hW]
      all_goals rfl
    rw [e1, if_pos ht, WithLp.toLp_smul, fL_interior hint, hpl]
    rfl

/-- The record's advice of round `a0 + s` in `IND` is the checked advice `advC` of piece C. -/
theorem adv_eq (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case DB ω) {a0 s : ℕ} (ht : a0 + s < n) {st : St d}
    (hmo : (BB).mode DB (a0 + s) ω = .run (((BB).ctx DB a0 ω).st ((BB).path DB a0 ω) s))
    (hW : modeO d n δ r0 R0 a WW (a0 + s) = .run st) :
    apAdv ((BB).adv (a0 + s) ω ((BB).mode DB (a0 + s) ω)) =
      apAdv (advC K orc CC (kDel δ) (fun s => apAdv ((BB).adv (a0 + s) ω ((BB).mode DB (a0 + s) ω)))
        ((BB).path DB a0 ω) s st (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1
        (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).2 ((WW).noise (a0 + s)) ((WW).f (a0 + s))) := by
  have hY := refYO_eq hI hc h hq ht rfl hmo
  rw [hmo]
  have e : (BB).adv (a0 + s) ω (.run (((BB).ctx DB a0 ω).st ((BB).path DB a0 ω) s)) =
      advQO orc CC n st (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1 (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).2
        (readO d n δ r0 R0 a WW (a0 + s)) (poO d n δ) (((BB).ctx DB a0 ω).st ((BB).path DB a0 ω) s)
        ((WE).xi (a0 + s) ω)
        (refYO n δ r0 R0 a orc h hI.convex (a0 + s) ω (((BB).ctx DB a0 ω).st ((BB).path DB a0 ω) s)) := by
    show advO n δ r0 R0 a orc h hI.convex (a0 + s) ω _ = _
    unfold advO
    rw [if_pos ht, hW]
    all_goals rfl
  rw [e, readO_eq _ hW, hY]
  rfl

/-- `IND(0)`. -/
theorem inv_zeroO (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case DB ω) : EngInvO n δ r0 R0 a orc h hI.convex ω 0 := by
  have hbud : BudOK d n (kDel δ) := budO d n δ hI.hd hI.hn hc
  have H := rowHyp_of d n (dBL d n δ) hI.hd hI.hn (deltaO_pos d n _ hI.hd hI.hn)
    (deltaO_lt_one d n _ hI.hd hI.hn) (hc.trans (by norm_num))
  have hR1 : 1 ≤ (poK d n (kDel δ)).R := row_one_le_R _ d n H
  have heps := (eps_factsK hI.hd hI.hn hc hbud).2.2.1
  have heps' : (parK d n (kDel δ)).eps ≤ 1 / 2 := by
    have h2 : (((parK d n (kDel δ)).eps : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by push_cast; exact heps
    exact Rat.cast_le.mp h2
  exact ⟨0, 0, init (parO d n δ) d, rfl, rfl, fun u hu => absurd hu (Nat.not_lt_zero u),
    modeO_zero hI _ rfl hq hR1 hbud.enc.R_le heps', track_initK hI.hd hI.hn hc hbud⟩

/-- `IND(t) → IND(t + 1)` at a round `t < n` that does not decouple, on `Case ∩ Ω_ref ∩ E_bits ∩ NoClip`: piece C
(`RoundCO`) in the epoch's round `s`, then Lemma HOR at a fire (a fresh epoch before round `t + 1`). -/
theorem inv_succO (hC : RoundCO) (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case DB ω) (hG : (BB).Good DB ω) (hbits : ω ∈ (BB).bits) {t : ℕ} (ht : t < n)
    (hD : ¬ (BB).D DB t ω) (hInv : EngInvO n δ r0 R0 a orc h hI.convex ω t) :
    EngInvO n δ r0 R0 a orc h hI.convex ω (t + 1) := by
  obtain ⟨a0, s, st, rfl, hfa, hcont, hW, htr⟩ := hInv
  have hreg : Regime d n DB := ⟨hI.hd, hI.hn, deltaO_pos d n _ hI.hd hI.hn, deltaO_lt_one d n _ hI.hd hI.hn,
    hc.trans (by norm_num)⟩
  obtain ⟨hmo, hdet, htau⟩ := RunW.round_ctx _ hreg hI.compact.isClosed hI.convex hq hG ht hfa hcont
  have hbud : BudOK d n (kDel δ) := budO d n δ hI.hd hI.hn hc
  have hY := cY_coupledO hI hc h hq ht rfl hmo hW hD
  rw [loss_eq h hI.convex ω ht, nz_eq h ω ht] at hY
  have hap := adv_eq hI hc h hq ht hmo hW
  have hb := hbits.1 (a0 + s) ht
  have hnz := hbits.2 (a0 + s) ht
  rw [nz_eq h ω ht] at hnz
  have hg := RunW.path_g _ hq ht
  rw [loss_eq h hI.convex ω ht] at hg
  have hadm : AdmLoss K ((WW).f (a0 + s)) := by
    rw [← loss_eq h hI.convex ω ht]
    exact (BB).F.adm (a0 + s) ht _
  have H : RCHypO K orc CC (kDel δ) (fun s => apAdv ((BB).adv (a0 + s) ω ((BB).mode DB (a0 + s) ω)))
      ((BB).path DB a0 ω) s st (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1 (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).2
      ((WE).zz (a0 + s) ω 0) ((WW).noise (a0 + s)) ((WW).f (a0 + s)) :=
    { hd := hI.hd, hn := hI.hn, par := rfl, hc := hc, bud := hbud, frame := frameW hI _, pg := hq,
      hs := by show s < n; omega, det := hdet, tau := htau, track := htr, adm := hadm,
      g := fun y => congrFun hg y, xi := hb.1, zt := hb.2, nz := hnz, Y := hY }
  have hRC := hC d K orc _ (kDel δ) _ ((BB).path DB a0 ω) s st _ _ _ _ _ H hap
  have hstep := modeO_succ_run (n := n) (δ := δ) (r0 := r0) (R0 := R0) (a := a) WW hW
  rcases hRC with ⟨hf1, hf2⟩ | ⟨st', hs1, hs2, hs3⟩
  · have hm1 : (BB).mode DB (a0 + s + 1) ω = .run (df2Init (poO d n δ) d) := by
      have h1 := RunW.vmode _ hreg hI.compact.isClosed hI.convex hq hfa (s + 1) (by omega)
      rw [← add_assoc] at h1
      rw [h1]
      exact hf2
    refine ⟨a0 + s + 1, 0, init (parO d n δ) d, by omega, hm1, fun u hu => absurd hu (Nat.not_lt_zero u), ?_,
      track_initK hI.hd hI.hn hc hbud⟩
    rw [hstep]
    exact hf1
  · refine ⟨a0, s + 1, st', by omega, hfa, ?_, ?_, hs3⟩
    · intro u hu
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
      · exact hcont u hu
      · exact hs2
    · rw [hstep]
      exact hs1

end Rec

/-- **`IND(t)` from piece C**: `RoundCO → IndO`. -/
theorem indO (hC : RoundCO) : IndO := by
  intro d n δ r0 R0 a K orc hI hc Ω _ μ coin loss noise h ω hq hG hbits t
  induction t with
  | zero => intro _ _; exact inv_zeroO hI hc h hq
  | succ t ih =>
    intro ht hD
    exact inv_succO hC hI hc h hq hG hbits (by omega) (hD t (by omega))
      (ih (by omega) fun u hu => hD u (by omega))

end AdversarialBco.Unified.Eng
