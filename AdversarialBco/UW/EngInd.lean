/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngRec
public import AdversarialBco.Unified.EngInd

@[expose] public section

/-!
# Step 1 of SHADOW for BL-OW's record: the induction `IND(t)`

Unified/EngInd.lean for BL-OW's record `recOW` and P° of Theorem UW at PARAM-W's reference `ρ = refW d n δ`, with
piece C (`RoundCOW`, UW/EngDefs.lean) as a hypothesis:

* the epoch start: `ε ≤ ε' ≤ 1/2`, `ε' - ε ≤ w_ε` and `TrackW` between BL-OW's and P°'s initial states
  (`eps_factsW`, `track_initW`, Lemma ENC-W), and BL-OW's first mode is `run` on `Case` (`modeOW_zero`: the cross
  check passes by `crossOKO` in the good position of radius `R ≤ R'`);
* the round: the record's advice is the checked advice `advCW` of piece C when the round does not decouple
  (`adv_eqW`; P°'s unweighted observation is then BL-OW's exact one, `refYOW_coupled`), and P°'s weighted observation
  is the weight and the clip of it (`ctx_YU`, `refYOW_eqU`);
* `inv_succOW`: `RCHypOW` from `Case`, `Ω_ref` and `E_bits`, then `RoundCOW`; `indOW : RoundCOW → IndOW`.

The regime of PARAM-W's reference in the case (`RegRefW`, the first clause of `SchedUW`) is a hypothesis.
-/

open MeasureTheory

namespace AdversarialBco.UW.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified (NoisyAdv envWorld)
open AdversarialBco.Unified.Eng (xO obsO goodPos_of_pg)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW
open AdversarialBco.Bit.BLP (Par St init cV cM opN)
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ}

/-! ## The epoch start -/

/-- Lemma ENC-W on `ε`: `0 < ε ≤ ε' ≤ 1/2` and `ε' - ε ≤ w_ε`. -/
theorem eps_factsW {n : ℕ} {δ : ℚ} (hreg : RegimeW d n (refW d n δ)) (henc : EncOKW d n δ) :
    0 < (poW d n δ).eps ∧ (poW d n δ).eps ≤ ((parOW d n δ).eps : ℝ) ∧ ((parOW d n δ).eps : ℝ) ≤ 1 / 2 ∧
      ((parOW d n δ).eps : ℝ) - (poW d n δ).eps ≤ (rW d n δ).we := by
  have h0 : 0 < (poW d n δ).eps := EvP.eps_pos hreg
  have h14 : (poW d n δ).eps ≤ 1 / 4 := hreg.heps
  have h1 : (poW d n δ).eps ≤ ((parOW d n δ).eps : ℝ) := henc.eps_le
  have h2 : ((parOW d n δ).eps : ℝ) ≤ (poW d n δ).eps * (1 + (rW d n δ).tp / 16) := henc.eps_rel
  have htp0 : 0 ≤ (rW d n δ).tp := by
    show 0 ≤ Unified.BudK.tp d n (kDel δ)
    unfold Unified.BudK.tp; positivity
  have htp1 : (rW d n δ).tp ≤ 1 := by
    show Unified.BudK.tp d n (kDel δ) ≤ 1
    unfold Unified.BudK.tp; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have ewe : (rW d n δ).we = (rW d n δ).tp / 16 * (poW d n δ).eps := rfl
  rw [ewe]
  refine ⟨h0, h1, ?_, ?_⟩ <;> nlinarith

/-- The level of event (a)'s gauge bound is BUD-W's `L_e`. -/
theorem leW_refW (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : leW (refW d n δ).δc = (rW d n δ).Le := by
  show df2C0 * Real.log (1 / (1 / ((NeO d n (kDel δ) : ℕ) : ℝ))) = Unified.BudK.Le d n (kDel δ)
  rw [Unified.BudK.Le_eq d n (kDel δ) hd hn, one_div_one_div, df2C0]
  rfl

/-- `TrackW` at the epoch start (Lemma ENC-W: `A_0`, `B_0`). -/
theorem track_initW {n : ℕ} {δ : ℚ} (hreg : RegimeW d n (refW d n δ)) (henc : EncOKW d n δ) :
    TrackW d n δ (init (parOW d n δ) d) (df2Init (poW d n δ) d) 0 := by
  have hs : 0 < (poW d n δ).sig2 := EvP.sig2_pos hreg
  set s := (poW d n δ).sig2 with hs_def
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq2 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have htp0 : 0 ≤ (rW d n δ).tp := by
    show 0 ≤ Unified.BudK.tp d n (kDel δ)
    unfold Unified.BudK.tp; positivity
  have hLf : (rW d n δ).Lf ≤ (rW d n δ).Le := by
    have h1 := EvP.Le_le_leW hreg
    have h2 := leW_refW d n δ hreg.hd hreg.hn
    have e : (rW d n δ).Lf = (parW d n (refW d n δ).u).Le := by rw [parW_Le]; rfl
    rw [e, ← h2]
    exact h1
  have hLf0 : 0 ≤ (rW d n δ).Lf := by
    have := regW_Le hreg.hd hreg.hn hreg.hu hreg.heps
    show 0 ≤ Bit.PieceA.Le d n
    linarith
  have hsqL : Real.sqrt (8 * (rW d n δ).Lf) ≤ Real.sqrt (8 * (rW d n δ).Le) :=
    Real.sqrt_le_sqrt (by linarith)
  have hha : (rW d n δ).hTr 0 = (rW d n δ).ha := by unfold RegW.hTr; simp
  have hha' : (rW d n δ).ha = (rW d n δ).tp * Real.sqrt (8 * (rW d n δ).Le) + (rW d n δ).tp +
      (rW d n δ).tp / 16 := by
    unfold RegW.ha; ring
  have hcM : ∀ c : ℚ, cM (c • (1 : Matrix (Fin d) (Fin d) ℚ)) = (c : ℝ) • 1 := by
    intro c; ext i j
    simp only [cM, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]; split_ifs <;> simp
  have hop : ∀ c : ℝ, opN (c • (1 : Matrix (Fin d) (Fin d) ℝ)) ≤ |c| := Bit.BLP.EngL.opN_smul_one d
  have hone : ∀ c : ℝ, (1 : Matrix (Fin d) (Fin d) ℝ) + (c - 1) • 1 = c • 1 := by
    intro c; rw [sub_smul, one_smul]; abel
  have hcV0 : cV (0 : Fin d → ℚ) = 0 := by funext i; simp [cV]
  have hst8 : 0 ≤ (rW d n δ).tp * Real.sqrt (8 * (rW d n δ).Le) := by positivity
  have hst8' : (rW d n δ).tp * Real.sqrt (8 * (rW d n δ).Lf) ≤ (rW d n δ).tp * Real.sqrt (8 * (rW d n δ).Le) :=
    mul_le_mul_of_nonneg_left hsqL htp0
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; simp [cV, init, df2Init]
  · show s • (1 : Matrix (Fin d) (Fin d) ℝ) = (Real.sqrt s • 1) * (Real.sqrt s • 1)ᵀ
    rw [Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul_comm, one_mul, hsq2]
  · show s⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) * s • 1 = 1
    rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hs.ne', one_smul]
  · refine ⟨(((parOW d n δ).A0 : ℝ) / Real.sqrt s - 1) • 1, ?_, ?_⟩
    · show cM ((parOW d n δ).A0 • 1) = _ * (Real.sqrt s • 1)
      rw [hcM, hone, smul_mul_smul_comm, one_mul, div_mul_cancel₀ _ hsq.ne']
    · refine (hop _).trans ?_
      rw [hha, hha']
      have := henc.A0
      linarith
  · refine ⟨(((parOW d n δ).B0 : ℝ) * Real.sqrt s - 1) • 1, ?_, ?_⟩
    · show cM ((parOW d n δ).B0 • 1) = _ * (s⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) * (Real.sqrt s • 1))
      rw [hcM, hone, smul_mul_smul_comm, one_mul, smul_mul_smul_comm, one_mul]
      congr 1
      field_simp
      rw [Real.sq_sqrt hs.le]
    · refine (hop _).trans ?_
      rw [hha, hha']
      have := henc.B0
      linarith
  · simp [oNorm, hcV0, init, df2Init]
  · simp [init, df2Init]
  · simp [oNorm, hcV0, init, df2Init]
  · simp [init, df2Init]

/-- The frame of BL-OW's configuration on an input of `TheoremUnified`. -/
theorem frameWW {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool}
    (hI : InpU n δ r0 R0 a K orc) (w : BitRAMO.WorldO d) : FrameO K orc (cfgWW d n δ r0 R0 a w) :=
  ⟨hI.convex, hI.compact.isClosed, hI.hr0, hI.hrR, hI.ball_in, hI.ball_out, hI.orc⟩

/-- **BL-OW starts in mode `run`** in a good position of radius `1 ≤ R ≤ R'` when `ε' ≤ 1/2`. -/
theorem modeOW_zero {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool}
    (hI : InpU n δ r0 R0 a K orc) (w : BitRAMO.WorldO d) (hw : w.orc = orc)
    (hq : PgGood d K (poW d n δ).R (some (cfgWW d n δ r0 R0 a w).S)) (hR1 : 1 ≤ (poW d n δ).R)
    (hR : (poW d n δ).R ≤ ((parOW d n δ).R : ℝ)) (heps : (parOW d n δ).eps ≤ 1 / 2) :
    modeOW d n δ r0 R0 a w 0 = .run (init (parOW d n δ) d) := by
  subst hw
  have hx : crossOK w.orc (cfgWW d n δ r0 R0 a w) :=
    crossOKO d K w.orc _ _ (frameWW hI w) (goodPos_of_pg hq) hR1 hR
  show mode0O w.orc (cfgWW d n δ r0 R0 a w) = _
  unfold mode0O
  rw [if_neg (show ¬ (1 / 2 < (cfgWW d n δ r0 R0 a w).par.eps) from not_lt.2 heps), if_pos hx]
  rfl

/-! ## The round -/

section Rec

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
  {orc : (Fin d → ℚ) → ℕ → Bool}

set_option hygiene false in
local notation "BB" => recOW n δ r0 R0 a orc h hI.convex
set_option hygiene false in
local notation "WE" => extO n δ r0 R0 a h
set_option hygiene false in
local notation "WW" => envWorld orc coin loss noise ω.1
set_option hygiene false in
local notation "CC" => cfgWW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)
set_option hygiene false in
local notation "RF" => refW d n δ

/-- The record's advice of round `t` in mode `run` on both sides, when the round does not decouple: the checked
advice at BL-OW's reading and BL-OW's exact observation. -/
theorem adv_eqW (hI : InpU n δ r0 R0 a K orc) (hreg : RegimeW d n RF)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case (RF).δc ω) {t : ℕ} (ht : t < n) {so : Df2St d} {st : St d}
    (hmo : modeU BB RF t ω = .run so) (hW : modeOW d n δ r0 R0 a WW t = .run st) (hD : ¬ DU BB RF t ω) :
    (BB).adv t ω (modeU BB RF t ω) =
      advQOW (b0OW d n δ) (y0OW d n δ) orc CC n st (drawO d n δ r0 R0 (coin ω.1) t).1
        (drawO d n δ r0 R0 (coin ω.1) t).2 (obsO orc CC st (drawO d n δ r0 R0 (coin ω.1) t).1 ((WW).f t)
          ((WW).noise t)) (poW d n δ) so ((WE).xi t ω)
        (YcO orc CC st (drawO d n δ r0 R0 (coin ω.1) t).1 ((WE).zz t ω 0) ((WW).noise t) ((WW).f t)) := by
  have hY := refYOW_coupled h hI.convex hreg hq ht hmo hW hD
  rw [loss_eqW h hI.convex ω ht, nz_eqW h ω ht] at hY
  rw [hmo]
  have e : (BB).adv t ω (.run so) =
      advQOW (b0OW d n δ) (y0OW d n δ) orc CC n st (drawO d n δ r0 R0 (coin ω.1) t).1
        (drawO d n δ r0 R0 (coin ω.1) t).2 (readOW d n δ r0 R0 a WW t) (poW d n δ) so ((WE).xi t ω)
        (refYOW n δ r0 R0 a orc h hI.convex t ω so) := by
    show advOW n δ r0 R0 a orc h hI.convex t ω _ = _
    unfold advOW
    rw [if_pos ht, hW]
  rw [e, readOW_eq _ hW, hY]
  rfl

/-- `IND(0)`. -/
theorem inv_zeroOW (hI : InpU n δ r0 R0 a K orc) (hreg : RegimeW d n RF)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case (RF).δc ω) : EngInvOW n δ r0 R0 a orc h hI.convex ω 0 := by
  have henc := encOKW d n δ hreg
  have hRW := rows_parW hreg.hd hreg.hn hreg.hu (by linarith [hreg.heps])
  have hR1 : 1 ≤ (poW d n δ).R := hRW.one_le_R
  have heps := (eps_factsW hreg henc).2.2.1
  have heps' : (parOW d n δ).eps ≤ 1 / 2 := by
    have h2 : (((parOW d n δ).eps : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by push_cast; exact heps
    exact Rat.cast_le.mp h2
  exact ⟨0, 0, init (parOW d n δ) d, rfl, rfl, fun u hu => absurd hu (Nat.not_lt_zero u),
    modeOW_zero hI _ rfl hq hR1 henc.R_le heps', track_initW hreg henc⟩

/-- `IND(t) → IND(t + 1)` at a round `t < n` that does not decouple, on `Case ∩ Ω_ref ∩ E_bits`: piece C
(`RoundCOW`) in the epoch's round `s`, then Lemma HOR at a fire (a fresh epoch before round `t + 1`). -/
theorem inv_succOW (hC : RoundCOW) (hRows : RowsUW) (hS : SIFactsUW) (hI : InpU n δ r0 R0 a K orc)
    (hc : RunCaseUW d n δ) (hreg : RegimeW d n RF)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case (RF).δc ω) (hG : GoodU BB RF ω) (hbits : ω ∈ (BB).bits) {t : ℕ} (ht : t < n)
    (hD : ¬ DU BB RF t ω) (hInv : EngInvOW n δ r0 R0 a orc h hI.convex ω t) :
    EngInvOW n δ r0 R0 a orc h hI.convex ω (t + 1) := by
  obtain ⟨a0, s, st, rfl, hfa, hcont, hW, htr⟩ := hInv
  obtain ⟨hmo, hdet, htau, hevG⟩ :=
    round_ctxU hRows hS hreg hI.compact.isClosed hI.convex hq hG ht hfa hcont
  have hbud : BudOKW d n (kDel δ) RF := budW d n (kDel δ) RF hreg
  have henc := encOKW d n δ hreg
  -- the observation
  have hrun := mode_run_of_cont _ _ s hcont
  have hYU := ctx_YU hq ht hrun
  have hrefY := refYOW_eqU h hI.convex hreg hq ht hmo
  have hY0 := refYOW_coupled h hI.convex hreg hq ht hmo hW hD
  rw [loss_eqW h hI.convex ω ht, nz_eqW h ω ht] at hY0
  have hY : (ctxU BB RF a0 ω).Y (epU BB RF a0 ω) s = obsW (RF).b0 (RF).y0 ((WE).xi (a0 + s) ω)
      (YcO orc CC st (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1 ((WE).zz (a0 + s) ω 0) ((WW).noise (a0 + s))
        ((WW).f (a0 + s))) := by
    rw [← hY0, hrefY]
    exact hYU
  have hb := hbits.1 (a0 + s) ht
  have hnz := hbits.2 (a0 + s) ht
  rw [nz_eqW h ω ht] at hnz
  have hg := path_gU hq ht (B := BB) (ρ := RF)
  rw [loss_eqW h hI.convex ω ht] at hg
  have hadm : AdmLoss K ((WW).f (a0 + s)) := by
    rw [← loss_eqW h hI.convex ω ht]
    exact (BB).F.adm (a0 + s) ht _
  have H : RCHypOW K orc CC δ (fun s => apAdv ((BB).adv (a0 + s) ω (modeU BB RF (a0 + s) ω)))
      (pathU BB RF a0 ω) s st (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1 (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).2
      ((WE).zz (a0 + s) ω 0) ((WW).noise (a0 + s)) ((WW).f (a0 + s)) :=
    { hd := hI.hd, hn := hI.hn, hδ0 := hI.hδ0, hδ1 := hI.hδ1, par := rfl, hc := hc, reg := hreg, bud := hbud,
      enc := henc, frame := frameWW hI _, pg := hq, hs := by show s < n; omega, det := hdet, tau := htau,
      evG := hevG, track := htr, adm := hadm, g := fun y => congrFun hg y, xi := hb.1, zt := hb.2, nz := hnz,
      Y := hY }
  have hap : (fun s => apAdv ((BB).adv (a0 + s) ω (modeU BB RF (a0 + s) ω))) s =
      apAdv (advCW K orc CC δ (fun s => apAdv ((BB).adv (a0 + s) ω (modeU BB RF (a0 + s) ω)))
        (pathU BB RF a0 ω) s st (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).1 (drawO d n δ r0 R0 (coin ω.1) (a0 + s)).2
        ((WE).zz (a0 + s) ω 0) ((WW).noise (a0 + s)) ((WW).f (a0 + s))) := by
    show apAdv ((BB).adv (a0 + s) ω (modeU BB RF (a0 + s) ω)) = _
    rw [adv_eqW hI hreg h hq ht hmo hW hD]
    rfl
  have hRC := hC d K orc _ δ _ (pathU BB RF a0 ω) s st _ _ _ _ _ H hap
  have hstep := modeOW_succ_run (n := n) (δ := δ) (r0 := r0) (R0 := R0) (a := a) WW hW
  rcases hRC with ⟨hf1, hf2⟩ | ⟨st', hs1, hs2, hs3⟩
  · have hm1 : modeU BB RF (a0 + s + 1) ω = .run (df2Init (poW d n δ) d) := by
      have h1 := vmodeU hreg hI.compact.isClosed hI.convex hq hfa (s + 1) (by omega)
      rw [← add_assoc] at h1
      rw [h1]
      exact hf2
    refine ⟨a0 + s + 1, 0, init (parOW d n δ) d, by omega, hm1, fun u hu => absurd hu (Nat.not_lt_zero u), ?_,
      track_initW hreg henc⟩
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

/-- **`IND(t)` from piece C**: `RoundCOW → IndOW`, in the regime of PARAM-W's reference. -/
theorem indOW (hC : RoundCOW) (hRows : RowsUW) (hS : SIFactsUW) (hReg : RegRefW) : IndOW := by
  intro d n δ r0 R0 a K orc hI hc Ω _ μ coin loss noise h ω hq hG hbits t
  have hreg := hReg d n δ hI.hd hI.hn hI.hδ0 hI.hδ1 hc
  induction t with
  | zero => intro _ _; exact inv_zeroOW hI hreg h hq
  | succ t ih =>
    intro ht hD
    exact inv_succOW hC hRows hS hI hc hreg h hq hG hbits (by omega) (hD t (by omega))
      (ih (by omega) fun u hu => hD u (by omega))

end AdversarialBco.UW.Eng
