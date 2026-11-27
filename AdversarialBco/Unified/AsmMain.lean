/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.AsmRec
public import AdversarialBco.Unified.ProgOBL
public import AdversarialBco.Unified.BLOGeom
public import AdversarialBco.Conj1Exp.Bound

@[expose] public section

/-!
# The assembly of `TheoremUnified`

`theoremUnified_of : AsmU → TheoremUnified`, with the program `P` of `theoremProg_of` (Unified/ProgOBL.lean), the
windows `DO`, `DO'` of BL-O (Unified/BLOSpec.lean) and `C = 10^29`. `AsmU` is the conjunction of the named
hypotheses, one `Prop` each:

* the program text (UNI-PROG, UNI-MACH): `ProgSetupO` and `ProgRoundO`, which give a
  program with `BLOLink` and `BLOMachOK`;
* the four W-hypotheses of SHADOW on BL-O's record `recO` (Unified/AsmRec.lean) on the extension `extO` of every
  environment with BL-O's windows, in the case `RunCaseO`, with their budgets in `δ`: `PosRecO` (`PosHypW` with
  `δpos ≤ δ/4`), `MeasRecO` (`BLMeasW`), `BitsRecO` (`BitsHypW` with `δbits ≤ δ/8`), `EngineRecO` (`EngineHypW` at
  `δ_BL` with `n (κ0 + κ1) ≤ δ/8`);
* the measurability of the regret on the environment's space (UNI-MEAS, `RegMeasU`);
* the arithmetic of the threshold at BL-O's confidence (`ThrO`).

The glue. The machine clauses are `BLOMachOK`, and the plays lie in `K` by `BLOLink` and `playIntO`. The regret lies
in `[-n, n]` (the losses are admissible, the plays in `K`), so it is integrable once measurable. In the case
`RunCaseO`, `shadow_env` with `shadowPropW_holds` bounds the probability of `{B_n + 1 < Reg}` by
`δpos + δ_ref + δbits + n (κ0 + κ1) ≤ δ/4 + δ/2 + δ/8 + δ/8`, and `B_n + 1 ≤ 10^29 d^{3/2} √n log(2dn/δ)^5`
(`ThrO`); off it `n` is below that threshold and the event is empty. The expectation: `max (Reg, 0) ≤ T + n 1_{T < Reg}`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Unified.Asm

open AdversarialBco AdversarialBco.Poly AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.ProgO
open AdversarialBco.BitRAM (toE State)
open AdversarialBco.BitRAMO (InstrO WorldO playedO)
open AdversarialBco.RealRAM (regretPts)

/-! ## The named hypotheses -/

/-- **(POS) for BL-O's record**: on every input in the run case and every environment with BL-O's windows, the
position of the record is known before round `0` and good off an event of probability at most `δpos ≤ δ/4`. -/
def PosRecO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseO d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      ∃ δpos : ℝ, 0 ≤ δpos ∧ δpos ≤ (δ : ℝ) / 4 ∧
        PosHypW (recO n δ r0 R0 a orc h hI.convex) (dBL d n δ) δpos

/-- **(O4-M) for BL-O's record**: the shift of round `t` is measurable at `F*_t` jointly with P°'s mode, the advice
at `𝓕 (t + 1)`. -/
def MeasRecO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseO d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      BLMeasW (recO n δ r0 R0 a orc h hI.convex)

/-- **(O4), the bit clause for BL-O's record**: the soundness event `E_bits ∩ NoClip` fails with probability at most
`δbits ≤ δ/8`. -/
def BitsRecO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseO d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      ∃ δbits : ℝ, 0 ≤ δbits ∧ δbits ≤ (δ : ℝ) / 8 ∧ BitsHypW (recO n δ r0 R0 a orc h hI.convex) δbits

/-- **Step 1 of SHADOW for BL-O's record** (pieces C, D with Theorem BUD at `parO`): on the case, `Ω_ref` and the
soundness event, before the first decoupling, the shift has `r > 0` and `tvB ≤ κ0 + κ1 |ε_t|`, and on no decoupling
BL-O's losses exceed P°'s by at most `1`; with `n (κ0 + κ1) ≤ δ/8`. -/
def EngineRecO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseO d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      ∃ κ0 κ1 : ℝ, 0 ≤ κ0 ∧ 0 ≤ κ1 ∧ (n : ℝ) * (κ0 + κ1) ≤ (δ : ℝ) / 8 ∧
        EngineHypW (recO n δ r0 R0 a orc h hI.convex) (dBL d n δ) κ0 κ1

/-- **UNI-MEAS**: on the environment's own space, the regret of a program whose plays of the rounds `t < n` lie in `K`
is measurable. -/
def RegMeasU : Prop :=
  ∀ (P : List InstrO) {d n : ℕ} (K : Set (E d)), (interior K).Nonempty → ∀ (s0 : State d), s0.rounds = 0 →
    ∀ (orc : (Fin d → ℚ) → ℕ → Bool) {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {coin : Ω → ℕ → Bool}
      {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} {D D' : ℕ → ℕ}, NoisyAdv K n D D' μ coin loss noise →
      (∀ ω, ∀ t < n, playedO P (envWorld orc coin loss noise ω) s0 t ∈ K) →
      Measurable fun ω => regretU P K n s0 (envWorld orc coin loss noise ω)

/-- The threshold of the theorem, `10^29 d^{3/2} √n log(2dn/δ)^5`. -/
noncomputable def thrU (d n : ℕ) (δ : ℚ) : ℝ :=
  10 ^ 29 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5

/-- **The arithmetic at BL-O's confidence** (UNI-DELTA, Lemma thr at `δ`): `0 < δ_BL < 1`, `δ_ref ≤ δ/2`, in the
run case `B_n + 1 ≤ thrU`, off it `n ≤ thrU`. -/
def ThrO : Prop :=
  ∀ (d n : ℕ) (δ : ℚ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 →
    0 < dBL d n δ ∧ dBL d n δ < 1 ∧ deltaRef d n (dBL d n δ) ≤ (δ : ℝ) / 2 ∧
      (RunCaseO d n δ → bReg d n (dBL d n δ) + 1 ≤ thrU d n δ) ∧ (¬ RunCaseO d n δ → (n : ℝ) ≤ thrU d n δ)

/-- The named hypotheses of the assembly. -/
structure AsmU : Prop where
  setup : ProgSetupO
  round : ProgRoundO
  pos : PosRecO
  meas : MeasRecO
  bits : BitsRecO
  engine : EngineRecO
  regMeas : RegMeasU
  thr : ThrO

/-! ## The regret clauses -/

theorem thrU_nonneg {d n : ℕ} {δ : ℚ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 ≤ thrU d n δ := by
  unfold thrU
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hL : 0 ≤ Real.log (2 * d * n / (δ : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0']
    nlinarith
  positivity

/-- The interior of `K` holds the centre `a`. -/
theorem interior_nonempty {d n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool}
    (hI : InpU n δ r0 R0 a K orc) : (interior K).Nonempty := by
  have hr : (0 : ℝ) < r0 := by exact_mod_cast hI.hr0
  exact ⟨toE a, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr)
    (Metric.ball_subset_closedBall.trans hI.ball_in))⟩

/-- The budget of the bad event: `δpos + δ_ref + δbits + n (κ0 + κ1) ≤ δ`. -/
theorem budget_le_delta {δ δpos δr δbits nk : ℝ} (hp : δpos ≤ δ / 4) (hr : δr ≤ δ / 2) (hb : δbits ≤ δ / 8)
    (hk : nk ≤ δ / 8) : δpos + δr + δbits + nk ≤ δ := by linarith

/-- **The regret clauses** of `TheoremUnified` for a program with `BLOLink` whose plays lie in `K`, from the named
hypotheses, on every environment with BL-O's windows. -/
theorem regret_of (h : AsmU) {P : List InstrO} (hL : BLOLink P) {d n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
    {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} (hI : InpU n δ r0 R0 a K orc)
    (hplayK : ∀ w : WorldO d, w.orc = orc → ∀ t < n, playedO P w (initU d n δ r0 R0 a) t ∈ K)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ}
    {noise : ℕ → Ω → ℝ} (hA : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) :
    Measurable (fun ω => regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) ∧
      Integrable (fun ω => regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) μ ∧
      μ {ω | thrU d n δ < regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)} ≤
        ENNReal.ofReal (δ : ℝ) ∧
      ∫ ω, max (regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) 0 ∂μ ≤
        thrU d n δ + n * (δ : ℝ) := by
  have := hA.prob
  set Reg : Ω → ℝ := fun ω => regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω) with hReg
  have hplay : ∀ ω, ∀ t < n, playedO P (envWorld orc coin loss noise ω) (initU d n δ r0 R0 a) t ∈ K :=
    fun ω => hplayK _ rfl
  have hadm : ∀ ω, ∀ t < n, AdmLoss K ((envWorld orc coin loss noise ω).f t) := fun ω t ht => hA.adm t ht ω
  have hle : ∀ ω, Reg ω ≤ n := fun ω => RealRAM.regretPts_le_of_mem (hadm ω) (hplay ω)
  have hge : ∀ ω, -(n : ℝ) ≤ Reg ω := fun ω => RealRAM.neg_le_regretPts_of_mem (hadm ω) (hplay ω)
  have hmeas : Measurable Reg :=
    h.regMeas P K (interior_nonempty hI) (initU d n δ r0 R0 a) rfl orc hA hplay
  have hint : Integrable Reg μ :=
    Integrable.of_bound hmeas.aestronglyMeasurable (n : ℝ)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_le]; exact ⟨hge ω, hle ω⟩)
  obtain ⟨hδBL0, hδBL1, hδref, hthr1, hthr2⟩ := h.thr d n δ hI.hd hI.hn hI.hδ0 hI.hδ1
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast hI.hδ0
  have hprob : μ {ω | thrU d n δ < Reg ω} ≤ ENNReal.ofReal (δ : ℝ) := by
    by_cases hc : RunCaseO d n δ
    · obtain ⟨δpos, hp0, hp1, hpos⟩ := h.pos d n δ r0 R0 a K orc hI hc Ω μ coin loss noise hA
      obtain ⟨δbits, hb0, hb1, hbits⟩ := h.bits d n δ r0 R0 a K orc hI hc Ω μ coin loss noise hA
      obtain ⟨κ0, κ1, hk0, hk1, hk2, heng⟩ := h.engine d n δ r0 R0 a K orc hI hc Ω μ coin loss noise hA
      have hM := h.meas d n δ r0 R0 a K orc hI hc Ω μ coin loss noise hA
      have hreg : Regime d n (dBL d n δ) := ⟨hI.hd, hI.hn, hδBL0, hδBL1, hc.trans (by norm_num)⟩
      have hS := shadow_env shadowPropW_holds (extO_ok n δ r0 R0 a hA) (recO n δ r0 R0 a orc hA hI.convex) P
        (initU d n δ r0 R0 a) orc (fun p t ht => recO_loss n δ r0 R0 a orc hA hI.convex p t ht)
        (fun p t ht => by
          rw [recO_play]
          exact (hL d n δ r0 R0 a hI.hd hI.hn hI.hδ0 hI.hδ1 hI.hr0 hI.hrR _ t ht).symm)
        δpos δbits κ0 κ1 hreg hI.compact.isClosed hI.convex hpos coupLaw_coupMax coupTV_coupMax hM hbits heng
        hp0 hb0 hk0 hk1
      calc μ {ω | thrU d n δ < Reg ω}
          ≤ μ {ω | bReg d n (dBL d n δ) + 1 < regEnv P K n (initU d n δ r0 R0 a) orc coin loss noise ω} :=
            measure_mono fun ω hω => lt_of_le_of_lt (hthr1 hc) hω
        _ ≤ ENNReal.ofReal (δpos + deltaRef d n (dBL d n δ) + δbits + n * (κ0 + κ1)) := hS
        _ ≤ ENNReal.ofReal (δ : ℝ) := ENNReal.ofReal_le_ofReal (budget_le_delta hp1 hδref hb1 hk2)
    · have he : {ω | thrU d n δ < Reg ω} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact (hle ω).trans (hthr2 hc)
      rw [he, measure_empty]
      exact bot_le
  refine ⟨hmeas, hint, hprob, ?_⟩
  -- the expectation: `max (Reg, 0) ≤ T + n 1_{T < Reg}`
  have hT := thrU_nonneg (δ := δ) hI.hd hI.hn hI.hδ0 hI.hδ1
  set S := {ω | thrU d n δ < Reg ω} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hmeas
  have hpt : ∀ ω, max (Reg ω) 0 ≤ thrU d n δ + n * S.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      exact max_le (by linarith [hle ω]) (by positivity)
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact max_le (not_lt.mp hω) hT
  have hi2 : Integrable (fun ω => thrU d n δ + n * S.indicator 1 ω) μ :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator hSm |>.const_mul _)
  have hreal : μ.real S ≤ δ := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hδ0.le hprob
  calc ∫ ω, max (Reg ω) 0 ∂μ ≤ ∫ ω, (thrU d n δ + n * S.indicator 1 ω) ∂μ :=
        integral_mono hint.pos_part hi2 hpt
    _ = thrU d n δ + n * μ.real S := by
        have h1 : Integrable (fun ω => (n : ℝ) * S.indicator (fun _ => (1 : ℝ)) ω) μ :=
          ((integrable_const (1 : ℝ)).indicator hSm).const_mul _
        rw [show (fun ω => thrU d n δ + n * S.indicator 1 ω) =
            fun ω => thrU d n δ + n * S.indicator (fun _ => (1 : ℝ)) ω from rfl,
          integral_add (integrable_const _) h1, integral_const, integral_const_mul, integral_indicator_const _ hSm]
        simp
    _ ≤ thrU d n δ + n * (δ : ℝ) := by gcongr

/-! ## The assembly -/

/-- **`TheoremUnified` from the named hypotheses**, with BL-O's program, its windows `DO`, `DO'` and `C = 10^29`. -/
theorem theoremUnified_of (h : AsmU) : TheoremUnified := by
  obtain ⟨P, C', k, hL, hM⟩ := theoremProg_of h.setup h.round
  refine ⟨P, 10 ^ 29, C', k, DO, DO', ?_⟩
  intro d hd n hn δ r0 R0 hδ0 hδ1 hr0 hrR a K hKc hKv hin hout orc horc
  have hI : InpU n δ r0 R0 a K orc := ⟨hd, hn, hδ0, hδ1, hr0, hrR, hKc, hKv, hin, hout, horc⟩
  have hplayK : ∀ w : WorldO d, w.orc = orc → ∀ t < n, playedO P w (initU d n δ r0 R0 a) t ∈ K := by
    intro w hw t ht
    rw [hL d n δ r0 R0 a hd hn hδ0 hδ1 hr0 hrR w t ht]
    exact interior_subset (playIntO d n δ r0 R0 a K w hd hr0 hKv hin (hw ▸ horc) t)
  refine ⟨fun f nz cs _ => ?_, fun Ω _ μ coin loss noise hA => ?_⟩
  · obtain ⟨hC, hS, hW⟩ := hM d n δ r0 R0 a hd hn hδ0 hδ1 hr0 hrR ⟨f, nz, cs, orc⟩
    exact ⟨hC, hS, hplayK _ rfl, hW⟩
  · exact regret_of h hL hI hplayK hA

end AdversarialBco.Unified.Asm
