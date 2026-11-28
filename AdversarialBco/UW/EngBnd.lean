/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngInd
public import AdversarialBco.UW.EngAsm
public import AdversarialBco.Unified.EngBnd

@[expose] public section

/-!
# Step 1 of SHADOW for BL-OW's record: the shift and the regret of a round

Unified/EngBnd.lean for BL-OW's record `recOW` and P° of Theorem UW at PARAM-W's reference, with piece C's play
(`PlayCOW`, UW/EngDefs.lean) as a hypothesis. The shift compares the unweighted observations, so the round's bound is
Theorem U's with the constants of Theorem BUD-W at `rW d n δ`:

* `shR_runOW`: the shift of a round at which both learners are in mode `run` is `r = pt'/pt°`,
  `m = (r - 1) ε_t + 2 (e'(X') - e(X°))/pt°`;
* `round_bndOW`: in `IND(t)`, `|X' - X°| ≤ X̄` (piece C's play), the gauge of P°'s point is at most `L_e^{1/2}`
  (event (a) at the level, `L_e` BUD-W's `Le`), and the gauge band of BL-OW's scale give `tvB(m, r) ≤ κ + κ |ε_t|`
  and the loss gap `regO/n` (the leaves `band_pt`, `shift_band`, `pt_band`, `tv_noise`, `shift_total`,
  `regret_total` of Unified/EngBnd.lean and `ext_lip_shift`, `play_gap` of Bit/BLEngLeaves.lean, unchanged);
* `engineRecW`: `EngineRecUW (implW P C' k)` from piece C (`RoundCOW`, `PlayCOW`) and the regime of PARAM-W's
  reference in the case (`RegRefW`).
-/

open MeasureTheory

namespace AdversarialBco.UW.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified (NoisyAdv envWorld)
open AdversarialBco.Unified.Eng (xO obsO goodPos_of_pg band_pt shift_band pt_band tv_noise shift_total regret_total
  kTh_eq_bodyS playPtO_run)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW
open AdversarialBco.Bit.BLP (Par St init cV cM opN)
open AdversarialBco.Bit.BLP.EngL (ptE extE)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.Poly.Conj1 (fL)
open Matrix

variable {d : ℕ}

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
set_option hygiene false in
local notation "XS" => (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (extO n δ r0 R0 a h).xi t ω))
set_option hygiene false in
local notation "KT" => kTh n (refW d n δ).δc K ((recOW n δ r0 R0 a orc h hI.convex).pos ω)
set_option hygiene false in
local notation "EP" => (poW d n δ).eps
set_option hygiene false in
local notation "PTO" => ptE KT EP (WithLp.toLp 2 XS)
set_option hygiene false in
local notation "XQ" =>
  XO (cfgWW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)) st (drawO d n δ r0 R0 (coin ω.1) t).1
set_option hygiene false in
local notation "PT1" => ((ptO orc (cfgWW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)) XQ : ℚ) : ℝ)
set_option hygiene false in
local notation "FF" => fun y => (recOW n δ r0 R0 a orc h hI.convex).loss ω t
  (pgMu ((recOW n δ r0 R0 a orc h hI.convex).pos ω) + pgOp ((recOW n δ r0 R0 a orc h hI.convex).pos ω) y)
set_option hygiene false in
local notation "EQ" => (((cfgWW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)).par.eps : ℚ) : ℝ)

/-- **BL-OW's shift of a round** at which both learners are in mode `run`: `r = pt'/pt°` and
`m = (r - 1) ε_t + 2 (e'(X') - e(X°))/pt°`, `e'(X') = pt' f(x')/2 + 2 (pt' - 1)/ε'` with the gauge play `pt'`. -/
theorem shR_runOW (hI : InpU n δ r0 R0 a K orc) (hreg : RegimeW d n RF)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case (RF).δc ω) {t : ℕ} (ht : t < n) {so : Df2St d} {st : St d}
    (hmo : modeU BB RF t ω = .run so) (hW : modeOW d n δ r0 R0 a WW t = .run st) :
    shRU BB RF t ω = ((PT1 / PTO - 1) * (WE).nz t ω +
      2 * ((PT1 * (FF) (PT1⁻¹ • toE XQ) / 2 + 2 * (PT1 - 1) / EQ) - extE KT EP (FF) (WithLp.toLp 2 XS)) / PTO,
      PT1 / PTO) := by
  obtain ⟨hrp, hint⟩ := refPlayU_runW h hI.convex hreg hq hmo
  rw [hrp] at hint
  have hpl : toE (playOW d n δ r0 R0 a WW t) = pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (PT1⁻¹ • toE XQ) := by
    have e : playOW d n δ r0 R0 a WW t = playPtO orc CC (.run st) (drawO d n δ r0 R0 (coin ω.1) t).1 := by
      unfold playOW
      rw [hW]
      rfl
    rw [e]
    exact playPtO_run orc CC st _
  refine Prod.ext ?_ ?_
  · have e1 : (shRU BB RF t ω).1 = (PT1 / PTO - 1) * (WE).nz t ω +
        (PT1 * (BB).F.L t ((BB).F.lam t ω) (toE (playOW d n δ r0 R0 a WW t)) -
          PTO * (if t < n then fL K (BB).F.L t ((BB).F.lam t ω) else 0)
            (pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (WithLp.toLp 2 (PTO⁻¹ • XS))) +
          4 * (PT1 - 1) / EQ - 4 * (PTO - 1) / EP) / PTO := by
      show (shOW n δ r0 R0 a orc h hI.convex t ω (modeU BB RF t ω)).1 = _
      rw [hmo]
      unfold shOW
      rw [if_pos ht, hW]
      all_goals rfl
    rw [e1, if_pos ht, WithLp.toLp_smul, fL_interior hint, hpl]
    show _ = _ + 2 * ((PT1 * (BB).F.L t ((BB).F.lam t ω)
        (pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (PT1⁻¹ • toE XQ)) / 2 + 2 * (PT1 - 1) / EQ) -
      (PTO * (BB).F.L t ((BB).F.lam t ω) (pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (PTO⁻¹ • WithLp.toLp 2 XS)) / 2 +
        2 * (PTO - 1) / EP)) / PTO
    ring
  · show (shOW n δ r0 R0 a orc h hI.convex t ω (modeU BB RF t ω)).2 = _
    rw [hmo]
    unfold shOW
    rw [if_pos ht, hW]
    all_goals rfl

/-- **The shift and the regret of a round** in `IND(t)` on `Case ∩ Ω_ref ∩ E_bits`, from piece C's play. -/
theorem round_bndOW (hP : PlayCOW) (hRows : RowsUW) (hS : SIFactsUW) (hI : InpU n δ r0 R0 a K orc)
    (hc : RunCaseUW d n δ) (hreg : RegimeW d n RF)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case (RF).δc ω) (hG : GoodU BB RF ω) (hbits : ω ∈ (BB).bits) {t : ℕ} (ht : t < n)
    (hInv : EngInvOW n δ r0 R0 a orc h hI.convex ω t) :
    (0 < (shRU BB RF t ω).2 ∧
      tvB (shRU BB RF t ω).1 (shRU BB RF t ω).2 ≤ (rW d n δ).kapO + (rW d n δ).kapO * |(WE).nz t ω|) ∧
    (BB).loss ω t ((BB).play t ω) ≤ (BB).loss ω t (refPlayU BB RF t ω) + (rW d n δ).regO / n := by
  obtain ⟨a0, s, st, hts, hfa, hcont, hW, htr⟩ := hInv
  have hd := hI.hd
  have hn := hI.hn
  obtain ⟨hmo, hdet, htau, hevG⟩ :=
    round_ctxU hRows hS hreg hI.compact.isClosed hI.convex hq hG (by omega : a0 + s < n) hfa hcont
  have hbud : BudOKW d n (kDel δ) RF := budW d n (kDel δ) RF hreg
  have henc := encOKW d n δ hreg
  have heps0 := EvP.eps_pos hreg
  have heps1 := EvP.eps_lt_one hreg
  obtain ⟨he0, hee, he', hwe⟩ := eps_factsW hreg henc
  -- piece C's play
  have hxe : (pathU BB RF a0 ω).xi s = (WE).xi t ω := by rw [← hts]; rfl
  have hxi : ∀ i, |((drawO d n δ r0 R0 (coin ω.1) t).1 i : ℝ) - (pathU BB RF a0 ω).xi s i| ≤
      4 / 2 ^ ((CC).par.B / 2) := by
    intro i
    rw [hxe]
    exact (hbits.1 t ht).1 i
  have hXP := hP d K CC δ (fun s => apAdv ((BB).adv (a0 + s) ω (modeU BB RF (a0 + s) ω)))
    (pathU BB RF a0 ω) s st (drawO d n δ r0 R0 (coin ω.1) t).1 hd hn rfl hc hreg hbud henc hq
    (by show s < n; omega) hdet htau hevG htr hxi
  have hg0' := (hevG s (by rw [htau])).2.1
  generalize hso : (ctxU BB RF a0 ω).st (epU BB RF a0 ω) s = so at hmo
  rw [hts] at hmo
  have hXeq : (ctxOW K CC δ (fun s => apAdv ((BB).adv (a0 + s) ω (modeU BB RF (a0 + s) ω)))).X
      (pwOW K CC δ (fun s => apAdv ((BB).adv (a0 + s) ω (modeU BB RF (a0 + s) ω))) (pathU BB RF a0 ω)) s = XS := by
    show ((ctxU BB RF a0 ω).st (epU BB RF a0 ω) s).mu + (1 - (poW d n δ).lam) •
      (((ctxU BB RF a0 ω).st (epU BB RF a0 ω) s).A *ᵥ (pathU BB RF a0 ω).xi s) = _
    rw [hso, hxe]
  have hX : ‖toE XQ - WithLp.toLp 2 XS‖ ≤ (rW d n δ).Xb := by
    have e : toE XQ = WithLp.toLp 2 (cV XQ) := rfl
    rw [e, ← WithLp.toLp_sub, ← LeanAp.oNorm_eq, ← hXeq]
    exact hXP
  have hg0 : gauge KT (WithLp.toLp 2 XS) ≤ Real.sqrt (rW d n δ).Le := by
    rw [← hXeq, ← leW_refW d n δ hd hn]
    exact hg0'
  -- the record's shift and plays
  obtain ⟨hrp, -⟩ := refPlayU_runW h hI.convex hreg hq hmo
  have hsh := shR_runOW hI hreg h hq ht hmo hW
  have hpl : (BB).play t ω = pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (PT1⁻¹ • toE XQ) := by
    show toE (playOW d n δ r0 R0 a WW t) = _
    have e : playOW d n δ r0 R0 a WW t = playPtO orc CC (.run st) (drawO d n δ r0 R0 (coin ω.1) t).1 := by
      unfold playOW
      rw [hW]
      rfl
    rw [e]
    exact playPtO_run orc CC st _
  have hL1 : (BB).loss ω t ((BB).play t ω) = (FF) (PT1⁻¹ • toE XQ) := (congrArg ((BB).loss ω t) hpl).trans rfl
  have hL0 : (BB).loss ω t (refPlayU BB RF t ω) = (FF) (PTO⁻¹ • WithLp.toLp 2 XS) :=
    (congrArg ((BB).loss ω t) hrp).trans rfl
  rw [hsh, hL1, hL0]
  -- the body and the loss on it
  have hRW := rows_parW hd hn hreg.hu (by linarith [hreg.heps])
  have hR1 : 1 ≤ (df2oPar d n (RF).δc).R := hRW.one_le_R
  have hmw : 1 / (df2oPar d n (RF).δc).R ≤ df2Mw d := by
    rw [show (df2oPar d n (RF).δc).R = 134 * d * Real.sqrt (Real.log (2 * d + 2)) from rfl]
    exact inv_R_le_df2Mw d hd
  have hLe17 : (17467 : ℝ) ≤ (rW d n δ).Le := hbud.Le_ge
  have hLe0 : 0 ≤ (rW d n δ).Le := by linarith
  have hbody : Df2Body d (df2oPar d n (RF).δc).R KT := body_kTh hI.compact.isClosed hI.convex hR1 hmw _
  obtain ⟨hconv, hclosed, h1, hRb, -⟩ := id hbody
  have hq' : PgGood d K (df2oPar d n (RF).δc).R (some ((BB).pos ω)) := hq
  have hf : AdmLoss K ((BB).loss ω t) := (BB).F.adm t ht _
  set F : E d → ℝ := FF with hF
  have hFa : AdmLoss KT F := by
    have hbg := body_good hI.compact.isClosed hI.convex hq'
    rw [kTh_good hq']
    refine ⟨⟨hbg.1, fun x hx y hy a' b' ha hb hab => ?_⟩, fun x hx => hf.2 _ hx.1⟩
    have := hf.1.2 hx.1 hy.1 ha hb hab
    simp only [smul_eq_mul] at this ⊢
    simp only [hF]
    rw [affine_comb _ x y a' b' hab]
    exact this
  have hlip : ∀ x y : E d, (1 - EP)⁻¹ • x ∈ KT → (1 - EP)⁻¹ • y ∈ KT → F y - F x ≤ ‖y - x‖ / EP :=
    fun x y hx hy => PropG.convex_lip_eps KT hconv h1 F hFa.1 hFa.2 _ heps0 heps1 x y hx hy
  have hconvF2 : ConvexOn ℝ KT (fun y => F y / 2) := by
    refine (hFa.1.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).congr fun y _ => ?_
    simp only [smul_eq_mul]; ring
  have hF2 : AdmLoss KT (fun y => F y / 2) :=
    ⟨hconvF2, fun x hx => ⟨by linarith [(hFa.2 x hx).1], by linarith [(hFa.2 x hx).2]⟩⟩
  have hSI := (hS d n (RF).u KT (fun y => F y / 2) hd hn hreg.hu (by linarith [hreg.heps]) hbody hF2).1.2.2.1
  have hext : ∀ x y : E d, |extE KT EP F x - extE KT EP F y| ≤ 8 / EP * ‖x - y‖ := by
    intro x y
    have e : ∀ z, df2Ext (parW d n (RF).u) KT (fun y => F y / 2) z = extE KT EP F z := by
      intro z
      show df2Ext (poW d n δ) KT (fun y => F y / 2) z = extE KT EP F z
      unfold df2Ext df2Pip extE ptE; ring
    have := hSI x y
    rwa [e, e] at this
  -- the gauge band
  have hRint : ((CC).par.R : ℝ) ≤ (CC).par.Rint := by
    have := Nat.le_ceil (parO d n δ).R
    show (((parO d n δ).R : ℚ) : ℝ) ≤ ((⌈(parO d n δ).R⌉₊ : ℕ) : ℝ)
    exact_mod_cast this
  have hGB := gaugeBandO d K orc CC (poW d n δ).R XQ hd (frameWW hI _) (goodPos_of_pg hq) hR1
    henc.R_le hRint
  have hKb : KT = bodyS K CC := kTh_eq_bodyS (c := CC) hq
  rw [← hKb] at hGB
  have hPT1 : PT1 = max 1 ((gaugeP orc CC XQ : ℝ) / (1 - EQ)) := by
    show ((max 1 (gaugeP orc CC XQ / (1 - (CC).par.eps)) : ℚ) : ℝ) = _
    push_cast
    rfl
  -- the vocabulary of Theorem BUD-W
  have eEP : (rW d n δ).eps = EP := rfl
  have eR : (rW d n δ).R = (df2oPar d n (RF).δc).R := rfl
  have epib : (rW d n δ).pib = Real.sqrt (rW d n δ).Le + 1 / 8 := rfl
  have egb : (rW d n δ).gb = (rW d n δ).tp / 2 * (rW d n δ).pib := rfl
  have ewe : (rW d n δ).we = (rW d n δ).tp / 16 * EP := rfl
  have empar : (rW d n δ).mpar =
      (rW d n δ).tp / 4 * (rW d n δ).pib * ((df2oPar d n (RF).δc).R + 10) / EP := rfl
  have eS : (rW d n δ).S = (2 + 16 / EP) * (rW d n δ).Xb + (rW d n δ).mpar := rfl
  have eband : (rW d n δ).band = (rW d n δ).gb *
      (2 + ((df2oPar d n (RF).δc).R * (rW d n δ).pib + 4) / EP) := rfl
  have ekap : (rW d n δ).kapO = 2 * ((rW d n δ).S + (rW d n δ).band) := rfl
  have ereg : (rW d n δ).regO = n / EP * ((1 + 2 * (df2oPar d n (RF).δc).R) * (rW d n δ).Xb +
      4 * (df2oPar d n (RF).δc).R * (rW d n δ).pib * (rW d n δ).we +
      (df2oPar d n (RF).δc).R * (rW d n δ).gb) := rfl
  have etp : 2 * (2 : ℝ)⁻¹ ^ ((CC).par.p + 2) = (rW d n δ).tp / 2 := by
    have e2 : (rW d n δ).tp = 1 / 2 ^ (CC).par.p := rfl
    rw [e2]
    generalize (CC).par.p = P
    rw [pow_add, inv_pow]
    field_simp
  have hee' : EP ≤ EQ := hee
  have he'' : EQ ≤ 1 / 2 := he'
  have hwe' : EQ - EP ≤ (rW d n δ).we := hwe
  have hpib1 : 1 ≤ (rW d n δ).pib := by
    rw [epib]
    have : (1 : ℝ) ≤ Real.sqrt (rW d n δ).Le := by
      rw [Real.one_le_sqrt]; linarith
    linarith
  have hR0 : 0 ≤ (df2oPar d n (RF).δc).R := by linarith
  have htp0 : 0 ≤ (rW d n δ).tp := by
    show 0 ≤ Unified.BudK.tp d n (kDel δ)
    unfold Unified.BudK.tp; positivity
  have hXb := hbud.Xb_le
  -- `π(X') ≤ π̄`
  have hgX : gauge KT (toE XQ) ≤ (rW d n δ).pib := by
    have hl := Bit.BLP.EngL.gauge_lip1 KT hconv h1 (toE XQ) (WithLp.toLp 2 XS)
    rw [epib]
    have := (abs_le.1 hl).2
    linarith
  -- the scale `pt'` against `pt_{ε'}(X')`
  have hη : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ ((CC).par.p + 2) := by positivity
  have hΔ : |PT1 - ptE KT EQ (toE XQ)| ≤ (rW d n δ).gb := by
    rw [hPT1, egb, ← etp]
    have := pt_band (gauge KT (toE XQ)) (gaugeP orc CC XQ : ℝ) EQ _ _ (gauge_nonneg _) hGB.1 hGB.2 hη he'' hgX
    rw [mul_assoc] at this ⊢
    exact this
  have hPT1g : gauge KT (toE XQ) / (1 - EQ) ≤ PT1 := by
    rw [hPT1]
    refine le_trans ?_ (le_max_right _ _)
    exact div_le_div_of_nonneg_right hGB.1 (by linarith)
  have hPT11 : 1 ≤ PT1 := by rw [hPT1]; exact le_max_left _ _
  obtain ⟨hb1, hb2⟩ := band_pt KT hconv hclosed h1 _ hRb F hFa.2 EP EQ heps0 hee' he'' hlip (toE XQ) PT1 hPT11
    hPT1g
  -- v2.1's bound at the scale `pt_{ε'}(X')`
  have h0 := Bit.BLP.EngL.ext_lip_shift KT hconv hclosed h1 _ hRb F hFa.2 EP EQ heps0 hee' he'' hlip hext
    (rW d n δ).Le (rW d n δ).Xb hLe0 hXb (toE XQ) (WithLp.toLp 2 XS) hg0 hX
  have hmp := Bit.BLP.EngL.mpar_le (rW d n δ).pib (df2oPar d n (RF).δc).R EP (EQ - EP) (rW d n δ).tp
    (by linarith) hR0 heps0 (by linarith) (by linarith) (by rw [← ewe]; exact hwe')
  rw [← epib] at h0
  have hpto : 1 ≤ PTO := le_max_left _ _
  have hsb := shift_band PT1 (ptE KT EQ (toE XQ)) PTO
    (PT1 * F (PT1⁻¹ • toE XQ) / 2 + 2 * (PT1 - 1) / EQ) (extE KT EQ F (toE XQ)) (extE KT EP F (WithLp.toLp 2 XS))
    (1 / 2 + ((df2oPar d n (RF).δc).R / 2 + 2) / EP) _ hpto h0 hb2
  have hS0 : (2 + 16 / EP) * (rW d n δ).Xb +
      (4 * (rW d n δ).pib * (EQ - EP) +
        2 * (rW d n δ).pib * ((df2oPar d n (RF).δc).R + 9) * (EQ - EP) / EP ^ 2) ≤ (rW d n δ).S := by
    rw [eS, empar]
    linarith
  have htot := shift_total _ _ _ _ _ _ _ _ hsb hS0 (abs_nonneg _) hΔ hR0 hpib1 heps0
  rw [← eband] at htot
  have hSl := hbud.S_le
  obtain ⟨hr, htv⟩ := tv_noise (PT1 / PTO) ((WE).nz t ω)
    (2 * ((PT1 * F (PT1⁻¹ • toE XQ) / 2 + 2 * (PT1 - 1) / EQ) - extE KT EP F (WithLp.toLp 2 XS)) / PTO)
    ((rW d n δ).S + (rW d n δ).band) htot hSl
  refine ⟨⟨hr, ?_⟩, ?_⟩
  · rw [ekap]
    exact htv
  · have hgap := Bit.BLP.EngL.play_gap KT hconv hclosed h1 _ hRb F EP EQ heps0 hee' he'' hlip
      (rW d n δ).Le (rW d n δ).Xb hLe0 hXb (toE XQ) (WithLp.toLp 2 XS) hg0 hX
    rw [← epib] at hgap
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [ereg]
    exact regret_total _ _ _ _ _ _ _ _ _ _ _ _ hgap hb1 hwe' hΔ hR0 (by linarith) heps0 hn0

theorem roundBndOW (hP : PlayCOW) (hRows : RowsUW) (hS : SIFactsUW) (hReg : RegRefW) : RoundBndOW := by
  intro d n δ r0 R0 a K orc hI hc Ω _ μ coin loss noise h ω hq hG hbits t ht hInv
  exact round_bndOW hP hRows hS hI hc (hReg d n δ hI.hd hI.hn hI.hδ0 hI.hδ1 hc) h hq hG hbits ht hInv

end Rec

/-- **Step 1 of SHADOW for BL-OW's record** from piece C: `EngineRecUW (implW P C' k)` given the round
(`RoundCOW`), the play (`PlayCOW`) and the regime of PARAM-W's reference in the case (`RegRefW`). -/
theorem engineRecW (hC : RoundCOW) (hP : PlayCOW) (hReg : RegRefW) (P : List BitRAMO.InstrO) (C' : ℝ) (k : ℕ) :
    EngineRecUW (implW P C' k) :=
  engineRecOW_of hReg (indOW hC rowsUW sifactsUW hReg) (roundBndOW hP rowsUW sifactsUW hReg) P C' k

end AdversarialBco.UW.Eng
