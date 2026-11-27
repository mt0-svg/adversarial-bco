/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.WorldShadow

@[expose] public section

/-!
# (O1) and SHADOW on an abstract coupled world

The port of Bit/ShadowWDet.lean, Bit/ShadowRef.lean, Bit/ShadowWEv.lean and the union bound of Bit/ShadowIface.lean
to a world `W : CWorld d Ω` with `WorldLawOK W`:

* `RunW.rr`, `RunW.wdet` (Proposition W-DET): on `Case ∩ Ω_ref`, P°'s regret is at most `B_n`;
* `RunW.epoch_bound`: the virtual epoch of P° started before round `a < n` is an instance of `Df2OnSetEAdV` on the
  filtration `W.𝓕` started at `a` (`setE_ref`, `setE_shift`);
* `wevPropW_holds`, `RunW.refProb`, `refPropW_holds : RefPropW`;
* `RunW.bad_subset`, `shadowPropW_of`, `shadowPropW_holds : ShadowPropW` (Proposition SHADOW).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.Unified.World

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Poly.Conj1 (fL)

variable {d : ℕ}

/-! ## Proposition W-DET -/

namespace RunW

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [m0 : MeasurableSpace Ω] {W : CWorld d Ω} (B : RunW d n K W) (δ : ℝ)

/-- The run record of P° on `ω`. -/
noncomputable def rr (ω : Ω) : RunRec d :=
  ⟨n, δ, K, B.loss ω, B.pos ω, fun t => apAdv (B.adv t ω (B.mode δ t ω)), fun t => W.xi t ω, fun t => W.nz t ω,
    fun t => B.zeta t ω (B.mode δ t ω)⟩

variable {B δ}

section Case

variable (hKconv : Convex ℝ K) {ω : Ω} (hq : B.Case δ ω) (heps0 : 0 < (df2oPar d n δ).eps)
  (heps1 : (df2oPar d n δ).eps < 1)
include hKconv hq heps0 heps1

theorem round_rr {t : ℕ} (ht : t < n) (m : Df2Mode d) :
    cRoundA n δ K (B.pos ω) (apAdv (B.adv t ω (B.mode δ t ω))) (B.lossR t ω) (W.nz t ω) (W.xi t ω)
      (B.zeta t ω (B.mode δ t ω)) m = (B.rr δ ω).rnd t m := by
  classical
  have hk : kTh n δ K (B.pos ω) = df2Kp K (B.pos ω) (df2oPar d n δ).R := kTh_good hq
  show df2RoundGa (df2oPar d n δ) n K (B.pos ω) (gauge (kTh n δ K (B.pos ω))) _ (B.lossR t ω) _ _ _ m =
    df2RoundGa (df2oPar d n δ) n K (B.pos ω) (gauge (df2Kp K (B.pos ω) (df2oPar d n δ).R)) _ (B.loss ω t) _ _ _ m
  rw [hk]
  refine roundGa_loss_congr hKconv hq heps0 heps1 n _ _ _ (fun y hy => ?_) _ _ _ m
  simp only [lossR, ht, ↓reduceIte, fL, loss, Set.piecewise_eq_of_mem _ _ _ hy]

theorem mode_rr : ∀ t ≤ n, B.mode δ t ω = (B.rr δ ω).mode t
  | 0, _ => rfl
  | t + 1, ht => by
    rw [RunRec.mode_succ, ← mode_rr t (by omega), ← round_rr hKconv hq heps0 heps1 (show t < n by omega)]
    rfl

theorem refPlay_rr {t : ℕ} (ht : t < n) : B.refPlay δ t ω = (B.rr δ ω).play t := by
  show (cRoundA n δ K (B.pos ω) _ (B.lossR t ω) _ _ _ (B.mode δ t ω)).1 = ((B.rr δ ω).rnd t ((B.rr δ ω).mode t)).1
  rw [round_rr hKconv hq heps0 heps1 ht, mode_rr hKconv hq heps0 heps1 t ht.le]

theorem mean_rr {t : ℕ} (ht : t < n) : B.mean δ t ω = (B.rr δ ω).mean t := by
  have hk : kTh n δ K (B.pos ω) = df2Kp K (B.pos ω) (df2oPar d n δ).R := kTh_good hq
  unfold mean RunRec.mean
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show B.loss ω t (df2RoundGa (df2oPar d n δ) n K (B.pos ω) (gauge (kTh n δ K (B.pos ω))) apCall (B.lossR t ω) 0 z
      0 (B.mode δ t ω)).1 = B.loss ω t (df2RoundGa (df2oPar d n δ) n K (B.pos ω)
      (gauge (df2Kp K (B.pos ω) (df2oPar d n δ).R)) apCall (B.loss ω t) 0 z 0 ((B.rr δ ω).mode t)).1
  rw [hk, mode_rr hKconv hq heps0 heps1 t ht.le, roundGa_fst _ _ _ _ _ _ (B.lossR t ω) (B.loss ω t) 0 0 z 0 0]

end Case

/-- On `Case`, the five events of the virtual epoch of P° started at `a` give `EpochOK` of the epoch of the record. -/
theorem epochOK_of_good (hAP : ∀ v : Adv d, ApSpec (apAdv v)) (hreg : Regime d n δ) (hKc : IsClosed K)
    (hKconv : Convex ℝ K) {ω : Ω} (hq : B.Case δ ω) {a : ℕ} (ha : a < n)
    (hev : (B.ctx δ a ω).EvG (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvY (B.path δ a ω) (n - a) ∧
      (B.ctx δ a ω).EvLQ (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvSDF (B.path δ a ω) (n - a) ∧
      (B.ctx δ a ω).EvDQ (B.path δ a ω) (n - a)) :
    ((B.rr δ ω).ctxAt a).EpochOK ((B.rr δ ω).pathAt a) (n - a) := by
  classical
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  obtain ⟨evG, evY, evLQ, evSDF, evDQ⟩ := hev
  have hE := df2DetF_holds (Kt := kTh n δ K (B.pos ω)) (fun s => apAdv (B.adv (a + s) ω (B.mode δ (a + s) ω)))
    (B.path δ a ω) hd hn hδ0 hδ1 heps (by omega) (Nat.sub_le n a) (body_kTh hKc hKconv hR hmw _)
    (fun s => hAP _) (fun s hs => adm_gTh (f := fun t => B.F.L t (lamAtW n B.F.lam a s ω)) (a := a) (s := s) hKconv
      hKc hR hmw (B.F.adm (a + s) (by omega) _) _)
    evG evY evLQ evSDF evDQ
  have hk : kTh n δ K (B.pos ω) = df2Kp K (B.pos ω) (df2oPar d n δ).R := kTh_good hq
  have hc : df2CtxAtF d n δ (kTh n δ K (B.pos ω)) (fun s => apAdv (B.adv (a + s) ω (B.mode δ (a + s) ω))) =
      (B.rr δ ω).ctxAt a := by
    rw [hk]; rfl
  rw [hc] at hE
  refine (ctx_epochOK_congr ((B.rr δ ω).ctxAt a) (B.path δ a ω) ((B.rr δ ω).pathAt a) (n - a) (by omega)
    fun s hs => ⟨?_, rfl, rfl⟩).mp hE
  funext y
  have has : a + s < n := by omega
  have hq' : PgGood d K (df2oPar d n δ).R (some (B.pos ω)) := hq
  show gTh n δ K (fun t => B.F.L t (lamAtW n B.F.lam a s ω)) a s (B.pos ω) y =
    B.F.L (a + s) (B.F.lam (a + s) ω) (pgMu (B.pos ω) + pgOp (B.pos ω) y) / 2
  simp only [gTh, hq', ↓reduceIte, lamAtW, has]

/-- Proposition W-DET: on `Case ∩ Ω_ref`, P°'s regret over the `n` rounds is at most `B_n`. -/
theorem wdet (hAP : ∀ v : Adv d, ApSpec (apAdv v)) (hreg : Regime d n δ) (hKc : IsClosed K)
    (hKconv : Convex ℝ K) {ω : Ω} (hq : B.Case δ ω) (hg : B.Good δ ω) :
    regretPts K (B.loss ω) (fun t => B.refPlay δ t ω) n ≤ bReg d n δ := by
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have heps0 := eps_pos_of_rows H
  have heps1 : (df2oPar d n δ).eps < 1 := by linarith
  have hplay : ∑ t ∈ Finset.range n, B.loss ω t (B.refPlay δ t ω) =
      ∑ t ∈ Finset.range n, (B.rr δ ω).f t ((B.rr δ ω).play t) :=
    Finset.sum_congr rfl fun t ht => by
      rw [refPlay_rr hKconv hq heps0 heps1 (Finset.mem_range.mp ht)]; rfl
  have hmean : ∑ t ∈ Finset.range n, B.mean δ t ω = ∑ t ∈ Finset.range n, (B.rr δ ω).mean t :=
    Finset.sum_congr rfl fun t ht => mean_rr hKconv hq heps0 heps1 (Finset.mem_range.mp ht)
  have haz := hg.2
  unfold Az at haz
  rw [hplay, hmean] at haz
  have h := (B.rr δ ω).det hd hn hδ0 hδ1 hKc hKconv (fun t ht => B.F.adm t ht _) hq heps
    (fun a ha => epochOK_of_good hAP ⟨hd, hn, hδ0, hδ1, heps⟩ hKc hKconv hq ha (hg.1 a ha)) haz
  unfold regretPts at h ⊢
  rw [hplay]
  exact h

/-! ## W-EV -/

theorem lamAtW_meas {a : ℕ} (ha : a < n) (s : ℕ) : Measurable[W.𝓕 (a + s)] (lamAtW n B.F.lam a s) := by
  unfold lamAtW
  by_cases h : a + s < n
  · simp only [h, ↓reduceIte]
    exact B.F.lam_meas (a + s) h
  · simp only [h, ↓reduceIte]
    exact (B.F.lam_meas a ha).mono (W.𝓕.mono (Nat.le_add_right a s)) le_rfl

/-- The virtual epoch of P° started before round `a < n` is an instance of the advice form of setting (E). -/
theorem epoch_bound {k : ℝ} {Bad : (d : ℕ) → Df2Ctx d → Df2Path d → ℕ → Prop} (h : Df2OnSetEAdV k Bad)
    (hW : WorldLawOK W) (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hpos : Measurable[W.𝓕 0] B.pos) (hC : CoupLaw B.Coup) (hB : BLMeasW B) {a : ℕ} (ha : a < n) :
    W.μ {ω | Bad d (B.ctx δ a ω) (B.path δ a ω) (n - a)} ≤ ENNReal.ofReal (k * (df2oPar d n δ).δe) := by
  have := hW.prob
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  have heps0 := eps_pos_of_rows H
  have heps1 : (df2oPar d n δ).eps < 1 := by linarith
  have hmode := mode_meas B δ hW ⟨hd, hn, hδ0, hδ1, heps⟩ hKc hKconv hpos hB hC
  have hE := setE_shift W.μ W.𝓕 W.xi (fun t => B.eRef δ t)
    (setE_ref hW hB hC ⟨hd, hn, hδ0, hδ1, heps⟩ hKc hKconv hpos) a
  have hθ : ∀ s, Measurable[fshift W.𝓕 a s] fun ω => (B.pos ω, lamAtW n B.F.lam a s ω) := fun s =>
    (hpos.mono (W.𝓕.mono (Nat.zero_le _)) le_rfl).prodMk (lamAtW_meas ha s)
  have hψ : ∀ s, Measurable[fshift W.𝓕 a (s + 1)] fun ω => B.adv (a + s) ω (B.mode δ (a + s) ω) := fun s =>
    adv_meas B δ hB (hmode (a + s))
  exact h d n (n - a) δ hd hn (by omega) (Nat.sub_le n a) hδ0 hδ1 heps (PgSp d × B.F.Λ) (Adv d)
    (fun x => kTh n δ K x.1) (fun s x => gTh n δ K (fun t => B.F.L t x.2) a s x.1) apAdv
    (fun x => body_kTh hKc hKconv hR hmw x.1)
    (fun x s hs => adm_gTh (f := fun t => B.F.L t x.2) hKconv hKc hR hmw (B.F.adm (a + s) (by omega) x.2) x.1)
    (apAdv_spec hd) (epochMeasV_inst hKc hKconv hR hmw heps0 heps1 B.F.adm B.F.meas a)
    Ω W.μ inferInstance (fshift W.𝓕 a)
    (fun s ω => (B.pos ω, lamAtW n B.F.lam a s ω)) (fun s ω => B.adv (a + s) ω (B.mode δ (a + s) ω))
    (fun s => W.xi (a + s)) (fun s => B.eRef δ (a + s)) hθ hψ (fun _ _ => rfl) hE

/-- The five events of the virtual epoch of P° started before round `a`, at its horizon `n - a`. -/
def Five (B : RunW d n K W) (δ : ℝ) (a : ℕ) (ω : Ω) : Prop :=
  (B.ctx δ a ω).EvG (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvY (B.path δ a ω) (n - a) ∧
    (B.ctx δ a ω).EvLQ (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvSDF (B.path δ a ω) (n - a) ∧
    (B.ctx δ a ω).EvDQ (B.path δ a ω) (n - a)

section Ref

variable (hW : WorldLawOK W) (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K)
  (hpos : Measurable[W.𝓕 0] B.pos) (hC : CoupLaw B.Coup) (hB : BLMeasW B)
include hW hreg hKc hKconv hpos hC hB

/-- The epoch started before round `a < n` misses one of its five events with probability at most
`(149/168) δe`. -/
theorem five_bound {a : ℕ} (ha : a < n) :
    W.μ {ω | B.Case δ ω ∧ ¬ B.Five δ a ω} ≤ ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe) := by
  obtain ⟨hG, hY, hLQ, hSDF, hDQ⟩ := df2EvBudgetsAdV
  have eG := epoch_bound hG hW hreg hKc hKconv hpos hC hB ha
  have eY := epoch_bound hY hW hreg hKc hKconv hpos hC hB ha
  have eLQ := epoch_bound hLQ hW hreg hKc hKconv hpos hC hB ha
  have eSDF := epoch_bound hSDF hW hreg hKc hKconv hpos hC hB ha
  have eDQ := epoch_bound hDQ hW hreg hKc hKconv hpos hC hB ha
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have hde : 0 ≤ (df2oPar d n δ).δe := (rowHyp_of d n δ hd hn hδ0 hδ1 heps).de_pos.le
  refine le_trans (measure_mono fun ω hω => hω.2) (union5 W.μ
    (fun ω => (B.ctx δ a ω).EvG (B.path δ a ω) (n - a))
    (fun ω => (B.ctx δ a ω).EvY (B.path δ a ω) (n - a))
    (fun ω => (B.ctx δ a ω).EvLQ (B.path δ a ω) (n - a))
    (fun ω => (B.ctx δ a ω).EvSDF (B.path δ a ω) (n - a))
    (fun ω => (B.ctx δ a ω).EvDQ (B.path δ a ω) (n - a)) _ hde eG eY eLQ eSDF eDQ)

/-- `Case` off `Ω_ref` has probability at most `δ_ref`. -/
theorem refProb : W.μ {ω | B.Case δ ω ∧ ¬ B.Good δ ω} ≤ ENNReal.ofReal (deltaRef d n δ) := by
  have hde : 0 ≤ (df2oPar d n δ).δe := by
    obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
    exact (rowHyp_of d n δ hd hn hδ0 hδ1 heps).de_pos.le
  have hsub : {ω | B.Case δ ω ∧ ¬ B.Good δ ω} ⊆
      (⋃ a ∈ Finset.range n, {ω | B.Case δ ω ∧ ¬ B.Five δ a ω}) ∪ {ω | B.Case δ ω ∧ ¬ B.Az δ ω} := by
    rintro ω ⟨hc, hg⟩
    by_cases hall : ∀ a < n, B.Five δ a ω
    · exact Or.inr ⟨hc, fun haz => hg ⟨hall, haz⟩⟩
    · obtain ⟨a, ha, hna⟩ : ∃ a < n, ¬ B.Five δ a ω :=
        by_contra fun hcon => hall fun a ha => by_contra fun hn => hcon ⟨a, ha, hn⟩
      exact Or.inl (Set.mem_biUnion (Finset.mem_range.mpr ha) ⟨hc, hna⟩)
  calc W.μ {ω | B.Case δ ω ∧ ¬ B.Good δ ω}
      ≤ W.μ ((⋃ a ∈ Finset.range n, {ω | B.Case δ ω ∧ ¬ B.Five δ a ω}) ∪ {ω | B.Case δ ω ∧ ¬ B.Az δ ω}) :=
        measure_mono hsub
    _ ≤ W.μ (⋃ a ∈ Finset.range n, {ω | B.Case δ ω ∧ ¬ B.Five δ a ω}) + W.μ {ω | B.Case δ ω ∧ ¬ B.Az δ ω} :=
        measure_union_le _ _
    _ ≤ ∑ a ∈ Finset.range n, W.μ {ω | B.Case δ ω ∧ ¬ B.Five δ a ω} + W.μ {ω | B.Case δ ω ∧ ¬ B.Az δ ω} :=
        add_le_add (measure_biUnion_finset_le _ _) le_rfl
    _ ≤ ∑ _a ∈ Finset.range n, ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe) +
          ENNReal.ofReal ((df2oPar d n δ).δe / 7) :=
        add_le_add (Finset.sum_le_sum fun a ha =>
          five_bound hW hreg hKc hKconv hpos hC hB (Finset.mem_range.mp ha))
          (waz hW hreg hKc hKconv hpos hB hC)
    _ = ENNReal.ofReal (deltaRef d n δ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, deltaRef,
        ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg n),
        ENNReal.ofReal_natCast]

end Ref

end RunW

/-- (O1) on an abstract coupled world. -/
theorem refPropW_holds : RefPropW := by
  intro d n δ K Ω _ W B hreg hKc hKconv hW hpos hC hB
  exact ⟨RunW.refProb hW hreg hKc hKconv hpos hC hB,
    fun ω hq hg => RunW.wdet (fun v => apAdv_spec hreg.1 v) hreg hKc hKconv hq hg⟩

/-! ## Proposition SHADOW -/

namespace RunW

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [MeasurableSpace Ω] {W : CWorld d Ω}

/-- On the good events, if no round decouples, BL's regret is at most `B_n + 1`; otherwise the first decoupled round
has a small shift. -/
theorem bad_subset (B : RunW d n K W) (δ κ0 κ1 : ℝ) (hE : EngineHypW B δ κ0 κ1)
    (hdet : ∀ ω, B.Case δ ω → B.Good δ ω → regretPts K (B.loss ω) (fun t => B.refPlay δ t ω) n ≤ bReg d n δ) :
    {ω | bReg d n δ + 1 < regretPts K (B.loss ω) (fun t => B.play t ω) n} ⊆
      {ω | ¬ B.Case δ ω} ∪ {ω | B.Case δ ω ∧ ¬ B.Good δ ω} ∪ B.bitsᶜ ∪
        ⋃ t ∈ Finset.range n, {ω | B.D δ t ω ∧ 0 < (B.shR δ t ω).2 ∧
          tvB (B.shR δ t ω).1 (B.shR δ t ω).2 ≤ κ0 + κ1 * |W.nz t ω|} := by
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  by_cases hC : B.Case δ ω
  swap
  · exact Or.inl (Or.inl (Or.inl hC))
  by_cases hG : B.Good δ ω
  swap
  · exact Or.inl (Or.inl (Or.inr ⟨hC, hG⟩))
  by_cases hb : ω ∈ B.bits
  swap
  · exact Or.inl (Or.inr hb)
  refine Or.inr ?_
  by_cases hD : ∃ t, t < n ∧ B.D δ t ω
  · classical
    let t := Nat.find hD
    have ht : t < n ∧ B.D δ t ω := Nat.find_spec hD
    have hmin : ∀ s < t, ¬ B.D δ s ω := fun s hs hs' =>
      Nat.find_min hD hs ⟨hs.trans ht.1, hs'⟩
    have hsh := hE.shift ω hC hG hb t ht.1 hmin
    simp only [Set.mem_iUnion, Finset.mem_range]
    exact ⟨t, ht.1, ht.2, hsh⟩
  · exfalso
    push Not at hD
    have hreg := hE.regret ω hC hG hb hD
    have hP := hdet ω hC hG
    unfold regretPts at hω hP
    linarith

end RunW

/-- Proposition SHADOW from (O1) and Step 2, on an abstract coupled world. -/
theorem shadowPropW_of (hRef : RefPropW) (hStep : CoupStepPropW) : ShadowPropW := by
  intro d n δ K Ω _ W B δpos δbits κ0 κ1 hreg hKc hKconv hW hpos hlaw htv hmeas hbits hE hδpos hδbits hκ0 hκ1
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have hde : 0 ≤ (df2oPar d n δ).δe := (Layer2.rowHyp_of d n δ hd hn hδ0 hδ1 heps).de_pos.le
  have hR := hRef d n δ K Ω W B ⟨hd, hn, hδ0, hδ1, heps⟩ hKc hKconv hW hpos.meas hlaw hmeas
  have hS := hStep d n δ K Ω W B κ0 κ1 ⟨hd, hn, hδ0, hδ1, heps⟩ hKc hKconv hW hpos.meas hlaw htv hmeas hκ0 hκ1
  have hdr : 0 ≤ deltaRef d n δ := by unfold deltaRef; positivity
  refine (measure_mono (RunW.bad_subset B δ κ0 κ1 hE hR.2)).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _)).trans ?_
  refine (add_le_add (add_le_add (measure_union_le _ _) hbits) (Finset.sum_le_sum fun t _ => hS t)).trans ?_
  refine (add_le_add (add_le_add (add_le_add hpos.bad hR.1) le_rfl) le_rfl).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_add hδpos hdr,
    ← ENNReal.ofReal_add (by positivity) hδbits, ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg n), ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- Proposition SHADOW on an abstract coupled world. -/
theorem shadowPropW_holds : ShadowPropW :=
  shadowPropW_of refPropW_holds coupStepPropW_holds

end AdversarialBco.Unified.World
