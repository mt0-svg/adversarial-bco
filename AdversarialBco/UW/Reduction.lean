/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Interfaces
public import AdversarialBco.Unified.AsmMeas

@[expose] public section

/-!
# Theorem UW from its interfaces

`theoremUW_of_all : AllUW I C → TheoremUW`: the conjunction of the interface Props of UW/Interfaces.lean implies
`TheoremUW`, with BL-OW's program `I.P`, the constant `C`, BL-O's windows `DO`, `DO'`. The assembly is Theorem U's
(Unified/WorldShadowRef.lean, Unified/WorldExt.lean, Unified/AsmMain.lean) with P° of Theorem UW in place of P°:

* `bad_subsetU`, `shadowPropUW_of : RefPropUW → CoupStepPropUW → ShadowPropUW` (Proposition SHADOW for P° of Theorem
  UW: the union bound of `shadowPropW_of`, with `GoodU`, `DU` and the budget `δ_ref(δc)`);
* `shadow_envUW` (`shadow_env`: SHADOW's bound on the environment's space);
* `regret_ofUW` (the four regret clauses; the measurability is Theorem U's `regMeasU`; in the case,
  SHADOW at PARAM's reference `refAt I d n δ` with the budget `δ/4 + δ/2 + δ/8 + δ/8`; off it, the trivial range);
* `theoremUW_of : AsmUW I C → TheoremUW`, `asmUW_of_all`, `theoremUW_of_all`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UW

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BLO (NeO kDel DO DO' BLOMachOK)
open AdversarialBco.Unified (NoisyAdv regretU initU envWorld)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (InstrO WorldO playedO)

variable {d : ℕ}

/-! ## Proposition SHADOW for P° of Theorem UW -/

/-- **Proposition SHADOW for P° of Theorem UW** (`ShadowPropW` with the reference `ρ`, `GoodU`, `DU`, `bRegW` and
the budget `δ_ref(δc)`). -/
def ShadowPropUW : Prop :=
  ∀ (d n : ℕ) (ρ : RefW) (K : Set (E d)) (Ω : Type) [MeasurableSpace Ω] (W : CWorld d Ω) (B : RunW d n K W)
    (δpos δbits κ0 κ1 : ℝ),
    RegimeW d n ρ → IsClosed K → Convex ℝ K → WorldLawOK W → PosHypW B ρ.δc δpos → CoupLaw B.Coup →
    CoupTV B.Coup → BLMeasW B → BitsHypW B δbits → EngineHypUW B ρ κ0 κ1 → 0 ≤ δpos → 0 ≤ δbits → 0 ≤ κ0 →
    0 ≤ κ1 →
      W.μ {ω | bRegW d n ρ.u ρ.δc + 1 < regretPts K (B.loss ω) (fun t => B.play t ω) n} ≤
        ENNReal.ofReal (δpos + deltaRefW n ρ.δc + δbits + n * (κ0 + κ1))

section Shadow

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [MeasurableSpace Ω] {W : CWorld d Ω}

/-- On the good events, if no round decouples, BL-OW's regret is at most `B_n + 1`; otherwise the first decoupled
round has a small shift (`RunW.bad_subset` for P° of Theorem UW). -/
theorem bad_subsetU (B : RunW d n K W) (ρ : RefW) (κ0 κ1 : ℝ) (hE : EngineHypUW B ρ κ0 κ1)
    (hdet : ∀ ω, B.Case ρ.δc ω → GoodU B ρ ω →
      regretPts K (B.loss ω) (fun t => refPlayU B ρ t ω) n ≤ bRegW d n ρ.u ρ.δc) :
    {ω | bRegW d n ρ.u ρ.δc + 1 < regretPts K (B.loss ω) (fun t => B.play t ω) n} ⊆
      {ω | ¬ B.Case ρ.δc ω} ∪ {ω | B.Case ρ.δc ω ∧ ¬ GoodU B ρ ω} ∪ B.bitsᶜ ∪
        ⋃ t ∈ Finset.range n, {ω | DU B ρ t ω ∧ 0 < (shRU B ρ t ω).2 ∧
          tvB (shRU B ρ t ω).1 (shRU B ρ t ω).2 ≤ κ0 + κ1 * |W.nz t ω|} := by
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  by_cases hC : B.Case ρ.δc ω
  swap
  · exact Or.inl (Or.inl (Or.inl hC))
  by_cases hG : GoodU B ρ ω
  swap
  · exact Or.inl (Or.inl (Or.inr ⟨hC, hG⟩))
  by_cases hb : ω ∈ B.bits
  swap
  · exact Or.inl (Or.inr hb)
  refine Or.inr ?_
  by_cases hD : ∃ t, t < n ∧ DU B ρ t ω
  · classical
    let t := Nat.find hD
    have ht : t < n ∧ DU B ρ t ω := Nat.find_spec hD
    have hmin : ∀ s < t, ¬ DU B ρ s ω := fun s hs hs' => Nat.find_min hD hs ⟨hs.trans ht.1, hs'⟩
    have hsh := hE.shift ω hC hG hb t ht.1 hmin
    simp only [Set.mem_iUnion, Finset.mem_range]
    exact ⟨t, ht.1, ht.2, hsh⟩
  · exfalso
    push Not at hD
    have hreg := hE.regret ω hC hG hb hD
    have hP := hdet ω hC hG
    unfold regretPts at hω hP
    linarith

end Shadow

/-- **(O1) for P° of Theorem UW** from W-SETE/W-EV (`EvProbUW`) and W-DET (`RefRegUW`). -/
theorem refPropUW_of (hEv : EvProbUW) (hReg : RefRegUW) : RefPropUW := by
  intro d n ρ K Ω _ W B hreg hKc hKv hW hpos hC hB
  exact ⟨hEv d n ρ K Ω W B hreg hKc hKv hW hpos hC hB, hReg d n ρ K Ω W B hreg hKc hKv⟩

/-- **Proposition SHADOW for P° of Theorem UW** from (O1) and Step 2 (`shadowPropW_of`). -/
theorem shadowPropUW_of (hRef : RefPropUW) (hStep : CoupStepPropUW) : ShadowPropUW := by
  intro d n ρ K Ω _ W B δpos δbits κ0 κ1 hreg hKc hKv hW hpos hlaw htv hmeas hbits hE hδpos hδbits hκ0 hκ1
  have hR := hRef d n ρ K Ω W B hreg hKc hKv hW hpos.meas hlaw hmeas
  have hS := hStep d n ρ K Ω W B κ0 κ1 hreg hKc hKv hW hpos.meas hlaw htv hmeas hκ0 hκ1
  have hdr : 0 ≤ deltaRefW n ρ.δc := by
    have := hreg.dc_pos
    unfold deltaRefW; positivity
  refine (measure_mono (bad_subsetU B ρ κ0 κ1 hE hR.2)).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _)).trans ?_
  refine (add_le_add (add_le_add (measure_union_le _ _) hbits) (Finset.sum_le_sum fun t _ => hS t)).trans ?_
  refine (add_le_add (add_le_add (add_le_add hpos.bad hR.1) le_rfl) le_rfl).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_add hδpos hdr,
    ← ENNReal.ofReal_add (by positivity) hδbits, ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg n), ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-! ## The glue to the environment -/

section Env

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {n : ℕ} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}

/-- SHADOW's bound for P° of Theorem UW on the environment's space (`shadow_env`). -/
theorem shadow_envUW (hS : ShadowPropUW) {ρ : RefW} {P0 B : ℕ} {W : CWorld d (Ω × (ℕ → ℝ))}
    (hE : ExtOK μ K n P0 B coin loss noise W) (R : RunW d n K W) (P : List InstrO) (s0 : BitRAM.State d)
    (orc : (Fin d → ℚ) → ℕ → Bool) (hloss : ∀ p, ∀ t < n, R.loss p t = loss t p.1)
    (hplay : ∀ p, ∀ t < n, R.play t p = playedO P (envWorld orc coin loss noise p.1) s0 t)
    (δpos δbits κ0 κ1 : ℝ) (hreg : RegimeW d n ρ) (hKc : IsClosed K) (hKv : Convex ℝ K)
    (hpos : PosHypW R ρ.δc δpos) (hC : CoupLaw R.Coup) (hTV : CoupTV R.Coup) (hM : BLMeasW R)
    (hb : BitsHypW R δbits) (hEng : EngineHypUW R ρ κ0 κ1) (h0 : 0 ≤ δpos) (h1 : 0 ≤ δbits) (h2 : 0 ≤ κ0)
    (h3 : 0 ≤ κ1) :
    μ {ω | bRegW d n ρ.u ρ.δc + 1 < regEnv P K n s0 orc coin loss noise ω} ≤
      ENNReal.ofReal (δpos + deltaRefW n ρ.δc + δbits + n * (κ0 + κ1)) := by
  have hS' := hS d n ρ K (Ω × (ℕ → ℝ)) W R δpos δbits κ0 κ1 hreg hKc hKv hE.law hpos hC hTV hM hb hEng h0 h1 h2 h3
  rw [hE.meas_eq] at hS'
  rw [← prob_ext μ {ω | bRegW d n ρ.u ρ.δc + 1 < regEnv P K n s0 orc coin loss noise ω}]
  refine le_trans (le_of_eq ?_) hS'
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, regEnv, regretU, regretPts]
  have hsum : ∑ t ∈ Finset.range n, (envWorld orc coin loss noise p.1).f t
      (playedO P (envWorld orc coin loss noise p.1) s0 t) =
      ∑ t ∈ Finset.range n, R.loss p t (R.play t p) :=
    Finset.sum_congr rfl fun t ht => by
      rw [hloss p t (Finset.mem_range.mp ht), hplay p t (Finset.mem_range.mp ht)]; rfl
  have hinf : (fun y => ∑ t ∈ Finset.range n, (envWorld orc coin loss noise p.1).f t y) =
      fun y => ∑ t ∈ Finset.range n, R.loss p t y :=
    funext fun y => Finset.sum_congr rfl fun t ht => by rw [hloss p t (Finset.mem_range.mp ht)]; rfl
  rw [hsum, hinf]

end Env

/-! ## The regret clauses and the assembly -/

theorem recUW_loss (I : ImplW) {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)}
    {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    (orc : (Fin d → ℚ) → ℕ → Bool) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise)
    (hK : Convex ℝ K) (p : Ω × (ℕ → ℝ)) (t : ℕ) (ht : t < n) :
    (recUW I n δ r0 R0 a orc h hK).loss p t = loss t p.1 :=
  recO_loss n δ r0 R0 a orc h hK p t ht

theorem recUW_play (I : ImplW) {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)}
    {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    (orc : (Fin d → ℚ) → ℕ → Bool) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise)
    (hK : Convex ℝ K) (p : Ω × (ℕ → ℝ)) (t : ℕ) :
    (recUW I n δ r0 R0 a orc h hK).play t p = toE (I.play d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) :=
  rfl

/-- **The regret clauses** of `TheoremUW` for BL-OW, from the named hypotheses, on every environment with BL-O's
windows. -/
theorem regret_ofUW {I : ImplW} {C : ℝ} (h : AsmUW I C) {d n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
    {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} (hI : InpU n δ r0 R0 a K orc)
    (hplayK : ∀ w : WorldO d, w.orc = orc → ∀ t < n, playedO I.P w (initU d n δ r0 R0 a) t ∈ K)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ}
    {noise : ℕ → Ω → ℝ} (hA : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) :
    Measurable (fun ω => regretU I.P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) ∧
      Integrable (fun ω => regretU I.P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) μ ∧
      μ {ω | thrUW C d n δ < regretU I.P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)} ≤
        ENNReal.ofReal (δ : ℝ) ∧
      ∫ ω, max (regretU I.P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) 0 ∂μ ≤
        thrUW C d n δ + n * (δ : ℝ) := by
  have := hA.prob
  set Reg : Ω → ℝ := fun ω => regretU I.P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω) with hReg
  have hplay : ∀ ω, ∀ t < n, playedO I.P (envWorld orc coin loss noise ω) (initU d n δ r0 R0 a) t ∈ K :=
    fun ω => hplayK _ rfl
  have hadm : ∀ ω, ∀ t < n, AdmLoss K ((envWorld orc coin loss noise ω).f t) := fun ω t ht => hA.adm t ht ω
  have hle : ∀ ω, Reg ω ≤ n := fun ω => RealRAM.regretPts_le_of_mem (hadm ω) (hplay ω)
  have hge : ∀ ω, -(n : ℝ) ≤ Reg ω := fun ω => RealRAM.neg_le_regretPts_of_mem (hadm ω) (hplay ω)
  have hmeas : Measurable Reg :=
    regMeasU I.P K (interior_nonempty hI) (initU d n δ r0 R0 a) rfl orc hA hplay
  have hint : Integrable Reg μ :=
    Integrable.of_bound hmeas.aestronglyMeasurable (n : ℝ)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_le]; exact ⟨hge ω, hle ω⟩)
  obtain ⟨hT, hδref, hthr1, hthr2⟩ := h.thr d n δ hI.hd hI.hn hI.hδ0 hI.hδ1
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast hI.hδ0
  have hprob : μ {ω | thrUW C d n δ < Reg ω} ≤ ENNReal.ofReal (δ : ℝ) := by
    by_cases hc : RunCaseUW d n δ
    · obtain ⟨hreg, hu0, hu1⟩ := h.sched d n δ hI.hd hI.hn hI.hδ0 hI.hδ1 hc
      obtain ⟨δpos, hp0, hp1, hpos⟩ := h.pos d n δ r0 R0 a K orc hI hc Ω μ coin loss noise hA
      obtain ⟨δbits, hb0, hb1, hbits⟩ := h.bits d n δ r0 R0 a K orc hI hc Ω μ coin loss noise hA
      obtain ⟨κ0, κ1, hk0, hk1, hk2, heng⟩ := h.engine d n δ r0 R0 a K orc hI hc Ω μ coin loss noise hA
      have hM := h.meas d n δ r0 R0 a K orc hI hc Ω μ coin loss noise hA
      have hS := shadow_envUW (shadowPropUW_of h.ref h.coup) (extO_ok n δ r0 R0 a hA)
        (recUW I n δ r0 R0 a orc hA hI.convex) I.P (initU d n δ r0 R0 a) orc
        (fun p t ht => recUW_loss I n δ r0 R0 a orc hA hI.convex p t ht)
        (fun p t ht => by
          rw [recUW_play]
          exact (h.link d n δ r0 R0 a hI.hd hI.hn hI.hδ0 hI.hδ1 hI.hr0 hI.hrR _ t ht).symm)
        δpos δbits κ0 κ1 hreg hI.compact.isClosed hI.convex hpos coupLaw_coupMax coupTV_coupMax hM hbits heng
        hp0 hb0 hk0 hk1
      calc μ {ω | thrUW C d n δ < Reg ω}
          ≤ μ {ω | bRegW d n (refAt I d n δ).u (refAt I d n δ).δc + 1 <
              regEnv I.P K n (initU d n δ r0 R0 a) orc coin loss noise ω} :=
            measure_mono fun ω hω => lt_of_le_of_lt (hthr1 hc _ hu0 hu1) hω
        _ ≤ ENNReal.ofReal (δpos + deltaRefW n (refAt I d n δ).δc + δbits + n * (κ0 + κ1)) := hS
        _ ≤ ENNReal.ofReal (δ : ℝ) := ENNReal.ofReal_le_ofReal (budget_le_delta hp1 hδref hb1 hk2)
    · have he : {ω | thrUW C d n δ < Reg ω} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact (hle ω).trans (hthr2 hc)
      rw [he, measure_empty]
      exact bot_le
  refine ⟨hmeas, hint, hprob, ?_⟩
  -- the expectation: `max (Reg, 0) ≤ T + n 1_{T < Reg}`
  set S := {ω | thrUW C d n δ < Reg ω} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hmeas
  have hpt : ∀ ω, max (Reg ω) 0 ≤ thrUW C d n δ + n * S.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      exact max_le (by linarith [hle ω]) (by positivity)
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact max_le (not_lt.mp hω) hT
  have hi2 : Integrable (fun ω => thrUW C d n δ + n * S.indicator 1 ω) μ :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator hSm |>.const_mul _)
  have hreal : μ.real S ≤ δ := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hδ0.le hprob
  calc ∫ ω, max (Reg ω) 0 ∂μ ≤ ∫ ω, (thrUW C d n δ + n * S.indicator 1 ω) ∂μ :=
        integral_mono hint.pos_part hi2 hpt
    _ = thrUW C d n δ + n * μ.real S := by
        have h1 : Integrable (fun ω => (n : ℝ) * S.indicator (fun _ => (1 : ℝ)) ω) μ :=
          ((integrable_const (1 : ℝ)).indicator hSm).const_mul _
        rw [show (fun ω => thrUW C d n δ + n * S.indicator 1 ω) =
            fun ω => thrUW C d n δ + n * S.indicator (fun _ => (1 : ℝ)) ω from rfl,
          integral_add (integrable_const _) h1, integral_const, integral_const_mul, integral_indicator_const _ hSm]
        simp
    _ ≤ thrUW C d n δ + n * (δ : ℝ) := by gcongr

/-- **`TheoremUW` from the named hypotheses of its assembly**, with BL-OW's program `I.P`, the constant `C`, BL-OW's
cost constants and BL-O's windows `DO`, `DO'`. -/
theorem theoremUW_of {I : ImplW} {C : ℝ} (h : AsmUW I C) : TheoremUW := by
  refine ⟨I.P, C, I.C', I.k, DO, DO', ?_⟩
  intro d hd n hn δ r0 R0 hδ0 hδ1 hr0 hrR a K hKc hKv hin hout orc horc
  have hI : InpU n δ r0 R0 a K orc := ⟨hd, hn, hδ0, hδ1, hr0, hrR, hKc, hKv, hin, hout, horc⟩
  have hplayK : ∀ w : WorldO d, w.orc = orc → ∀ t < n, playedO I.P w (initU d n δ r0 R0 a) t ∈ K := by
    intro w hw t ht
    rw [h.link d n δ r0 R0 a hd hn hδ0 hδ1 hr0 hrR w t ht]
    exact interior_subset (h.playInt d n δ r0 R0 a K w hd hr0 hKv hin (hw ▸ horc) t)
  refine ⟨fun f nz cs _ => ?_, fun Ω _ μ coin loss noise hA => ?_⟩
  · obtain ⟨hC, hS, hW⟩ := h.mach d n δ r0 R0 a hd hn hδ0 hδ1 hr0 hrR ⟨f, nz, cs, orc⟩
    exact ⟨hC, hS, hplayK _ rfl, hW⟩
  · exact regret_ofUW h hI hplayK hA

/-- The bricks and their routes give the named hypotheses of the assembly. -/
theorem asmUW_of_all {I : ImplW} {C : ℝ} (h : AllUW I C) : AsmUW I C where
  mach := h.mach
  link := h.link
  playInt := h.playInt
  sched := h.sched
  pos := h.pos
  meas := h.meas
  bits := h.bits
  engine := h.engineOf h.dom
  ref := refPropUW_of (h.evProbOf h.rows h.condIncr h.condBias h.lemmaUSet) (h.refRegOf (h.detOf h.rows h.sifacts))
  coup := h.coup
  thr := h.thr

/-- **`TheoremUW` from every brick of its proof and the routes between them.** -/
theorem theoremUW_of_all {I : ImplW} {C : ℝ} (h : AllUW I C) : TheoremUW :=
  theoremUW_of (asmUW_of_all h)

end AdversarialBco.UW
