/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PosRat
public import AdversarialBco.Bit.TriStage
public import AdversarialBco.Lemmas
public import AdversarialBco.Poly.PosGaussProof

@[expose] public section

/-!
# UNI-POS part 3: the stages of TRI-OGD-O on a body given through its SEP field

UNI-POS (the paper's section on the position), part 3. The procedure of TRI-OGD-O is that of TRI-OGD
(Bit/TriStage.lean) with the subgradient of the active row replaced by the program's SEP vector `gs j P z` (stage `j`,
position `P` of the previous stage, base point `z = μ + L w`), at the parameters of Unified/PosRow.lean
(`N' = 2^{n'}`, the step `2^{-j_s'}`, `G_up'`). The body `K` enters the procedure only through `gs` (the program
computes it from the oracle); it enters the analysis through `PosSepHyp` (Unified/PosSep.lean).

* `exSub`, `selAn`: the selection of the analysis, the program's vector at the rational base points of norm at most
  `triRz d`, an exact subgradient of the gauge elsewhere (`AdversarialBco.sg_exists`). It satisfies (SEP0) at every
  point (`selAn_sep0`) and agrees with the program's vector at every point the procedure reaches.
* `triCoreOutT`, `triCoreStageT`: the core on a stage body, a good position outside probability `δ`, from
  `triCoreTau` with `S` the rational points of `PgSp d` and `W` the rational vectors.
* `triStepT`, `triStageNT`, `triPosT`: stage `j` from `P` on its coins, the stages, the position on the coin stream;
  `triStage_inputK` (the input of a stage on the good event of the earlier ones), `isRatPg_triStageNT` (the positions
  are rational), `triStepT_meas`, `triStageNT_meas`, `triPosT_meas`.
* `triStagesT`, `triPosT_bad`: **Theorem TRI-OGD-O**: on the frame `B̄(c, r0) ⊆ K ⊆ B̄(c, R0)` (rational `c`, `r0`),
  under `PosSepHyp` with a slope `as ≤ 1/64` and `16 τ_s ≤ e_lo`, the position is good for `K` at the radius
  `36.4 d λ(ρ_h)` outside an event of probability `δ`.
* **The rule when SEP fails.** `gs` is any total function, measurable in `(P, z)`; the program sets `g = 0` when SEP
  fails (any other measurable rule serves). The analysis reads (SEP0) only at the stage of a position `P` for which
  `TriStageGood K c r0 j P` holds (the good event of the stages before `j`); off that event the union bound of
  `triStagesT` charges nothing to stage `j` (its event `C j` is empty there), so what the step does there is never
  used. `upos_measurable_of_countable` and `upos_countable_ratPt` give the measurability of a field read off a
  function on rational points and set to `0` elsewhere.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.UniPos

open AdversarialBco.Poly AdversarialBco.Bit

variable {d : ℕ}

/-! ## The selection of the analysis -/

open Classical in
/-- An exact subgradient of the gauge of `Kb` at `z` of norm at most `1` (when one exists; `0` otherwise). -/
noncomputable def exSub (Kb : Set (EuclideanSpace ℝ (Fin d))) (z : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  if h : ∃ s : EuclideanSpace ℝ (Fin d), ‖s‖ ≤ 1 ∧ ∀ z', gauge Kb z + inner ℝ s (z' - z) ≤ gauge Kb z' then
    h.choose else 0

open Classical in
/-- The selection of the analysis: the program's vector `g z` at the rational points of norm at most `triRz d`, an
exact subgradient of the gauge elsewhere. -/
noncomputable def selAn (Kb : Set (EuclideanSpace ℝ (Fin d))) (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if IsRatE z ∧ ‖z‖ ≤ triRz d then g z else exSub Kb z

theorem exSub_spec (Kb : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (hKb : PgBody Kb ρ) (z : EuclideanSpace ℝ (Fin d)) :
    ∀ z', gauge Kb z + inner ℝ (exSub Kb z) (z' - z) ≤ gauge Kb z' := by
  classical
  have hlip := (tri_gauge Kb hKb.1 hKb.2.2.1).1
  have hnhds : Kb ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) hKb.2.2.1
  have hconv := AdversarialBco.Poly.gauge_convexOn Kb hKb.1 hnhds
  obtain ⟨s, hs, hsub⟩ := AdversarialBco.sg_exists (gauge Kb) hconv 1 hlip z
  have hex : ∃ s : EuclideanSpace ℝ (Fin d), ‖s‖ ≤ 1 ∧ ∀ z', gauge Kb z + inner ℝ s (z' - z) ≤ gauge Kb z' :=
    ⟨s, by simpa using hs, hsub⟩
  unfold exSub
  rw [dif_pos hex]
  exact hex.choose_spec.2

/-- The selection of the analysis satisfies (SEP0) at every point. -/
theorem selAn_sep0 (Kb : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (hKb : PgBody Kb ρ)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (as cs : ℝ) (has0 : 0 ≤ as) (hcs0 : 0 ≤ cs)
    (hsep : ∀ z, IsRatE z → ‖z‖ ≤ triRz d → Sep0 (gauge Kb) z (g z) as cs) (z : EuclideanSpace ℝ (Fin d)) :
    Sep0 (gauge Kb) z (selAn Kb g z) as cs := by
  classical
  unfold selAn
  split_ifs with h
  · exact hsep z h.1 h.2
  · intro z'
    have h1 := exSub_spec Kb ρ hKb z z'
    have h2 : 0 ≤ as * ‖z' - z‖ := mul_nonneg has0 (norm_nonneg _)
    linarith

/-- The base points of the box have norm at most `triRz d`. -/
theorem tri_base_norm (x : PgSp d) (hx : x ∈ triBox d (triR d) (triA d) (triB d)) (w : EuclideanSpace ℝ (Fin d))
    (hw : ‖w‖ ≤ Real.sqrt (8 * d * triKg d)) : ‖pgMu x + pgOp x w‖ ≤ triRz d := by
  have hA0 : 0 ≤ triA d := by unfold triA; positivity
  have hR0 : 0 ≤ triR d := by unfold triR; positivity
  obtain ⟨hμ, -, -, -⟩ := (tri_box_iff (triR d) (triA d) (triB d) x).1 hx
  have hmu : ‖pgMu x‖ ≤ Real.sqrt d * triR d := by
    rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hR0, ← Real.sqrt_mul (Nat.cast_nonneg d)]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖pgMu x i‖ ^ 2 ≤ ∑ _i : Fin d, triR d ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          exact sq_le_sq' (abs_le.1 (hμ i)).1 (abs_le.1 (hμ i)).2
      _ = d * triR d ^ 2 := by simp
  have hop := tri_opNorm (triR d) (triA d) (triB d) hA0 x hx
  have hb0 : 0 ≤ triB d * Real.sqrt (d * (d + 1) / 2) := le_trans (norm_nonneg _) hop
  calc ‖pgMu x + pgOp x w‖ ≤ ‖pgMu x‖ + ‖pgOp x‖ * ‖w‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl ((pgOp x).le_opNorm w))
    _ ≤ Real.sqrt d * triR d + triB d * Real.sqrt (d * (d + 1) / 2) * Real.sqrt (8 * d * triKg d) :=
        add_le_add hmu (mul_le_mul hop hw (norm_nonneg _) hb0)

/-! ## The core on a stage body -/

/-- The core of TRI-OGD-O with the field `g` on the draws `y`: the average of `N' = 2^{n'}` steps of rounded projected
descent on the box, from `(0, I)`, with the vector `g` at the base points. -/
noncomputable def triCoreOutT (d ℓ : ℕ) (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (y : ℕ → EuclideanSpace ℝ (Fin d)) : PgSp d :=
  triAvg (triR d) (triA d) (triB d) (1 / 2 ^ triJsT d ℓ) (fun x w => triRound (triBv d) (triV g x w)) y
    (2 ^ triNeT d ℓ)

/-- **Theorem TRI-OGD-O, core** on a body `Kb` with `PgBody Kb ρ_a`: if the program's vector `g` satisfies (SEP0) for
the gauge of `Kb` at the rational base points of norm at most `triRz d`, with `0 ≤ as ≤ 1/64`, `0 ≤ cs` and
`16 τ_s ≤ e_lo`, `τ_s = as (1 + M_d) Δ + cs`, and the draws are independent with the sampler law, bounded and
rational, the core returns a good position for `Kb` outside an event of probability `δ`. -/
theorem triCoreStageT (d : ℕ) (hd : 1 ≤ d) (Kb : Set (EuclideanSpace ℝ (Fin d))) (hKb : PgBody Kb (triRa d))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hgm : Measurable g)
    (as cs : ℝ) (has0 : 0 ≤ as) (hcs0 : 0 ≤ cs) (has : as ≤ 1 / 64)
    (hτ : 16 * (as * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d)) + cs) ≤ triElo d)
    (hsep : ∀ z, IsRatE z → ‖z‖ ≤ triRz d → Sep0 (gauge Kb) z (g z) as cs)
    (ℓ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hℓ : Real.log (1 / δ) ≤ ℓ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hy : ∀ t, Measurable (y t)) (hind : iIndepFun y P)
    (hlaw : ∀ t, P.map (y t) = gsLaw d (4 * triKg d))
    (hyM : ∀ t ω, ‖y t ω‖ ≤ Real.sqrt (2 * d * (4 * triKg d : ℕ))) (hyQ : ∀ t ω, IsRatE (y t ω)) :
    P {ω | ¬ PgGood d Kb (36.4 * d * pgLam (triRh d)) (some (triCoreOutT d ℓ g fun t => y t ω))} ≤
      ENNReal.ofReal δ := by
  classical
  obtain ⟨hρa, hρρ, hr, ha0, ha, ha1, hb1, hb⟩ := tri_par_box d hd
  obtain ⟨hGT0, hGT⟩ := tri_par_GuT d hd as has0 has
  obtain ⟨hD0, hrow⟩ := tri_par_row_tau d ℓ hd δ hδ0 hδ1 hℓ
    (as * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d)) + cs) hτ
  have hkg : 2 ≤ triKg d := le_max_left _ _
  have hB8 : 8 ≤ 4 * triKg d := by omega
  obtain ⟨hlip, hgn⟩ := tri_gauge Kb hKb.1 hKb.2.2.1
  have hb0 : 0 ≤ triB d := by linarith
  -- the coupling of the objective on the box
  have hcpl : ∀ x ∈ triBox d (triR d) (triA d) (triB d),
      |∫ w, gauge Kb (pgMu x + pgOp x w) ∂(gsLaw d (4 * triKg d)) - posK Kb (pgMu x) (pgOp x)| ≤ triEpsG d := by
    intro x hx
    have h1 := gs_cpl d (4 * triKg d) hB8 (gauge Kb) hlip (fun z => by rw [abs_of_nonneg (hgn z).1]; exact (hgn z).2)
      (pgMu x) (pgOp x)
    have h2 := tri_opNorm (triR d) (triA d) (triB d) ha0.le x hx
    have h3 := tri_epsG_le d (triKg d) hd hkg (triB d) hb0
    have hε : 0 ≤ gsEps (4 * triKg d) := by unfold gsEps; positivity
    unfold posK posF
    refine h1.trans ((mul_le_mul_of_nonneg_right h2 (by positivity)).trans ?_)
    unfold triEpsG
    convert h3 using 2
  have hVt : Measurable (Function.uncurry fun x w => triRound (triBv d) (triV g x w)) :=
    (tri_round_meas (triBv d)).comp (tri_V_meas g hgm)
  have hΔ0 : 0 < Real.sqrt (triD2 d) := Real.sqrt_pos.2 hD0
  have hΔ : 4 * d * triR d ^ 2 + d * (triB d - triA d) ^ 2 + 2 * d * (d - 1) * triB d ^ 2 ≤
      Real.sqrt (triD2 d) ^ 2 := by rw [Real.sq_sqrt hD0.le]; rfl
  have hyM' : ∀ t ω, ‖y t ω‖ ≤ Real.sqrt (8 * d * triKg d) := by
    intro t ω
    refine (hyM t ω).trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hs : IsQ (1 / 2 ^ triJsT d ℓ : ℝ) := isQ_one.div (isQ_two_pow _)
  have hτs0 : 0 ≤ as * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d)) + cs := by positivity
  -- the program's field agrees with the selection of the analysis at the points the procedure reaches
  have hβ : ∀ x ∈ triBox d (triR d) (triA d) (triB d), x ∈ {x : PgSp d | IsRatPg x} →
      ∀ w ∈ {w : EuclideanSpace ℝ (Fin d) | IsRatE w}, ‖w‖ ≤ Real.sqrt (8 * d * triKg d) →
        ‖triRound (triBv d) (triV g x w) - triV (selAn Kb g) x w‖ ≤ triBu d := by
    intro x hx hxq w hwq hw
    have hsel : selAn Kb g (pgMu x + pgOp x w) = g (pgMu x + pgOp x w) := by
      unfold selAn
      rw [if_pos ⟨isRatE_base x hxq w hwq, tri_base_norm x hx w hw⟩]
    have hV : triV (selAn Kb g) x w = triV g x w := by
      unfold triV; rw [hsel]
    rw [hV]
    exact tri_round_err (triBv d) _
  exact triCoreTau d hd (triRa d) (triRh d) hρa hρρ Kb hKb (triR d) (triA d) (triB d) hr ha0 ha ha1 hb1 hb
    (selAn Kb g) as cs (Real.sqrt (8 * d * triKg d)) has0
    (fun x _ w _ => selAn_sep0 Kb _ hKb g as cs has0 hcs0 hsep _) (gsLaw d (4 * triKg d)) (triEpsG d) hcpl
    (fun x w => triRound (triBv d) (triV g x w)) hVt (triBu d) (triGuT d) (Real.sqrt (triD2 d))
    (1 / 2 ^ triJsT d ℓ) (as * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d)) + cs) hGT0 hGT hΔ0 hΔ
    (by positivity) hτs0 le_rfl {x | IsRatPg x} {w | IsRatE w} isRatPg_pgPack01
    (fun x hx w _ => isRatPg_triClip _ _ _ (isQ_triR d) (isQ_triA d) (isQ_triB d) _
      (IsRatPg.sub hx (IsRatPg.smul hs (isRatPg_triRound _ _))))
    hβ (2 ^ triNeT d ℓ) (by positivity) δ hδ0 hδ1 hrow P y hy hind hlaw hyM' hyQ

/-! ## The stages -/

/-- The coins of one stage of TRI-OGD-O: `N' = 2^{n'}` draws of `2 d B_g` coins. -/
noncomputable def triLT (d ℓ : ℕ) : ℕ := 2 ^ triNeT d ℓ * (2 * d * triBg d)

/-- Stage `j` from the position `P` on the coins `x` of the stage: the core with the program's field `gs j P`,
composed with `P`. -/
noncomputable def triStepT (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (ℓ j : ℕ)
    (P : PgSp d) (x : ℕ → Bool) : PgSp d :=
  pgComp P (triCoreOutT d ℓ (gs j P) fun t => triDraw d (triBg d) x t)

/-- The position after the stages `0, ..., j - 1`, from `P_0 = (c, r0 I)`, stage `i` on the coins `ω i`. -/
noncomputable def triStageNT (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (ℓ : ℕ) (ω : ℕ → ℕ → Bool) : ℕ → PgSp d
  | 0 => pgPack c (r0 • 1)
  | j + 1 => triStepT gs ℓ j (triStageNT gs c r0 ℓ ω j) (ω j)

/-- The position returned by TRI-OGD-O on the coin stream `cs`: stage `j` reads the coins `j L', ..., j L' + L' - 1`. -/
noncomputable def triPosT (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) (r0 R0 : ℝ) (ℓ : ℕ) (cs : ℕ → Bool) : PgSp d :=
  triStageNT gs c r0 ℓ (fun j k => cs (triLay (triMst r0 R0) (triLT d ℓ) (j, k))) (triMst r0 R0)

theorem triStageNT_dep (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (ℓ : ℕ) (ω ω' : ℕ → ℕ → Bool) (j : ℕ) (h : ∀ i < j, ω i = ω' i) :
    triStageNT gs c r0 ℓ ω j = triStageNT gs c r0 ℓ ω' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [triStageNT, ih fun i hi => h i (Nat.lt_succ_of_lt hi), h j (Nat.lt_succ_self j)]

/-- The positions of the stages are rational for a rational frame. -/
theorem isRatPg_triStageNT (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) (hc : IsRatE c) (r0 : ℝ) (hr0 : IsQ r0) (ℓ : ℕ) (ω : ℕ → ℕ → Bool) (j : ℕ) :
    IsRatPg (triStageNT gs c r0 ℓ ω j) := by
  induction j with
  | zero => exact isRatPg_start c hc r0 hr0
  | succ j ih =>
    exact isRatPg_pgComp _ _ ih (isRatPg_triAvg _ _ _ _ (isQ_triR d) (isQ_triA d) (isQ_triB d)
      (isQ_one.div (isQ_two_pow _)) _ _ _ _)

theorem triStepT_meas (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (ℓ j : ℕ)
    (hgs : Measurable fun q : PgSp d × EuclideanSpace ℝ (Fin d) => gs j q.1 q.2) :
    Measurable fun p : PgSp d × (ℕ → Bool) => triStepT gs ℓ j p.1 p.2 := by
  have hV := tri_V_meas2 (fun θ z => gs j θ z) hgs
  have hVt : Measurable fun q : PgSp d × PgSp d × EuclideanSpace ℝ (Fin d) =>
      triRound (triBv d) (triV (gs j q.1) q.2.1 q.2.2) := by
    simpa only [Function.comp_def] using (tri_round_meas (d := d) (triBv d)).comp hV
  have hA := (triIter_meas2 (triR d) (triA d) (triB d) (1 / 2 ^ triJsT d ℓ)
    (fun θ x w => triRound (triBv d) (triV (gs j θ) x w)) hVt).2 (2 ^ triNeT d ℓ)
  have hY : Measurable fun x : ℕ → Bool => fun t => triDraw d (triBg d) x t :=
    (tri_draw_facts d (triBg d) (triBg_ge d)).2.1
  have hg : Measurable fun p : PgSp d × (ℕ → Bool) => (p.1, fun t => triDraw d (triBg d) p.2 t) :=
    measurable_fst.prodMk (hY.comp measurable_snd)
  have hout : Measurable fun p : PgSp d × (ℕ → Bool) =>
      triAvg (triR d) (triA d) (triB d) (1 / 2 ^ triJsT d ℓ)
        (fun x w => triRound (triBv d) (triV (gs j p.1) x w))
        (fun t => triDraw d (triBg d) p.2 t) (2 ^ triNeT d ℓ) := by
    simpa only [Function.comp_def] using hA.comp hg
  have hfin := (PgMeas.pgComp_continuous d).measurable.comp (measurable_fst.prodMk hout)
  simpa only [Function.comp_def, triStepT, triCoreOutT] using hfin

theorem triStageNT_meas (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgs : ∀ j, Measurable fun q : PgSp d × EuclideanSpace ℝ (Fin d) => gs j q.1 q.2)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (ℓ j : ℕ) :
    Measurable fun ω : ℕ → ℕ → Bool => triStageNT gs c r0 ℓ ω j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih => exact (triStepT_meas gs ℓ j (hgs j)).comp (ih.prodMk (measurable_pi_apply j))

theorem triStageGoodK_meas (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (j : ℕ) :
    MeasurableSet {P : PgSp d | TriStageGood K c r0 j P} := by
  cases j with
  | zero => simp [TriStageGood]
  | succ i =>
    exact PgMeas.pgGoodMeas d _ _
      (hKc.inter (AdversarialBco.Bit.Aux_tri_stage0_body.t0b_convex_triCube c _))
      (hKcl.inter (AdversarialBco.Bit.Aux_tri_stage0_body.t0b_closed_triCube c _))

/-- The input of stage `j` for a body `K` (convex, closed, `B̄(c, r0) ⊆ K`): on the good event of the earlier
stages, an invertible position and a stage body between the unit ball and `B̄(0, ρ_a)`, for a general body. -/
theorem triStage_inputK (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (hr0 : 0 < r0) (hK0 : Metric.closedBall c r0 ⊆ K) (j : ℕ)
    (P : PgSp d) (hP : j = 0 → P = pgPack c (r0 • 1)) (hg : TriStageGood K c r0 j P) :
    (pgMat P).det ≠ 0 ∧ PgBody (posBody (K ∩ triCube c (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (triRa d) := by
  obtain ⟨hpar1, hpar2, -⟩ := tri_par_stage d hd
  have hcK : c ∈ K := hK0 (Metric.mem_closedBall_self hr0.le)
  cases j with
  | zero =>
    rw [hP rfl]
    obtain ⟨hdet, hbody⟩ := tri_stage0_body K hKc hKcl c r0 hr0 hK0
    refine ⟨hdet, ?_⟩
    have e : (2 : ℝ) ^ (0 + 1) * r0 = 2 * r0 := by ring
    rw [e]
    exact pgBody_mono _ _ _ hpar2 hbody
  | succ i =>
    obtain ⟨P', hP', hdet, h1, hR, -⟩ := hg
    obtain rfl := Option.some.inj hP'
    set s := (2 : ℝ) ^ (i + 1) * r0 with hs
    have hs0 : 0 ≤ s := by positivity
    obtain ⟨hcs, hsub, hmid⟩ := tri_cube_mid K hKc c hcK s hs0
    have hc2 := AdversarialBco.Bit.Aux_tri_stage0_body.t0b_convex_triCube c (2 * s)
    have hcl2 := AdversarialBco.Bit.Aux_tri_stage0_body.t0b_closed_triCube c (2 * s)
    have e : (2 : ℝ) ^ (i + 1 + 1) * r0 = 2 * s := by rw [hs]; ring
    rw [e]
    refine ⟨hdet, pgBody_mono _ _ _ hpar1 ?_⟩
    exact tri_stage_body (K ∩ triCube c s) (K ∩ triCube c (2 * s)) (hKc.inter hc2) (hKcl.inter hcl2) hsub c hcs
      hmid P hdet _ h1 hR

/-- **Theorem TRI-OGD-O, the stages**: on independent coin streams, one per stage, under `PosSepHyp`, the position
after the last stage is good for `K` at the radius `36.4 d λ(ρ_h)` outside an event of probability `δ`. -/
theorem triStagesT (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (c : EuclideanSpace ℝ (Fin d)) (hcq : IsRatE c) (r0 R0 : ℝ) (hr0q : IsQ r0) (hr0 : 0 < r0)
    (hK0 : Metric.closedBall c r0 ⊆ K) (hKR : K ⊆ Metric.closedBall c R0)
    (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgs : ∀ j, Measurable fun q : PgSp d × EuclideanSpace ℝ (Fin d) => gs j q.1 q.2)
    (as cs : ℝ) (has0 : 0 ≤ as) (hcs0 : 0 ≤ cs) (has : as ≤ 1 / 64)
    (hτ : 16 * (as * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d)) + cs) ≤ triElo d)
    (hsep : PosSepHyp K c r0 gs as cs) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ℓ : ℕ) (hℓ : Real.log (triMst r0 R0 / δ) ≤ ℓ) :
    (Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream)
      {ω | ¬ PgGood d K (36.4 * d * pgLam (triRh d)) (some (triStageNT gs c r0 ℓ ω (triMst r0 R0)))} ≤
        ENNReal.ofReal δ := by
  classical
  set M := triMst r0 R0 with hM
  obtain ⟨hm1, hmR⟩ := tri_mst r0 R0 hr0
  have hm0 : (0 : ℝ) < M := by exact_mod_cast hm1
  set δ' := δ / M with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ0 hm0
  have hδ'1 : δ' < 1 := (div_le_self hδ0.le (by exact_mod_cast hm1)).trans_lt hδ1
  have hℓ' : Real.log (1 / δ') ≤ ℓ := by rw [hδ', one_div_div]; exact hℓ
  -- the draws of a stage
  set B := triBg d with hB
  obtain ⟨hyM, hYm, -⟩ := tri_draw_facts d B (triBg_ge d)
  have hy : ∀ t, Measurable fun x : ℕ → Bool => triDraw d B x t := fun t => (measurable_pi_apply t).comp hYm
  have hlawJ := tri_draws_law d B
  have hlaw : ∀ t, AdversarialBco.BitRAM.coinStream.map (fun x => triDraw d B x t) = gsLaw d B := by
    intro t
    have e : (fun x => triDraw d B x t) = (fun f : ℕ → EuclideanSpace ℝ (Fin d) => f t) ∘
        (fun x t => triDraw d B x t) := rfl
    rw [e, ← Measure.map_map (measurable_pi_apply t) hYm, hlawJ, Measure.infinitePi_map_eval]
  have hind : iIndepFun (fun t x => triDraw d B x t) AdversarialBco.BitRAM.coinStream := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map hy, hlawJ]
    congr 1
    funext t
    rw [hlaw t]
  -- the event of stage `j`: good after `j` stages, not good after `j + 1`
  let C : ℕ → Set ((ℕ → ℕ → Bool) × (ℕ → Bool)) := fun j =>
    {q | TriStageGood K c r0 j (triStageNT gs c r0 ℓ q.1 j) ∧
      ¬ TriStageGood K c r0 (j + 1) (triStageNT gs c r0 ℓ (Function.update q.1 j q.2) (j + 1))}
  have hCm : ∀ j, MeasurableSet (C j) := fun j =>
    ((triStageGoodK_meas K hKc hKcl c r0 j).preimage ((triStageNT_meas gs hgs c r0 ℓ j).comp measurable_fst)).inter
      ((triStageGoodK_meas K hKc hKcl c r0 (j + 1)).preimage
        ((triStageNT_meas gs hgs c r0 ℓ (j + 1)).comp measurable_update')).compl
  have hE : ∀ j, (Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream) {ω | (ω, ω j) ∈ C j} ≤
      ENNReal.ofReal δ' := by
    intro j
    refine slice_resample AdversarialBco.BitRAM.coinStream j (C j) (hCm j) ?_ _ ?_
    · intro ω x x'
      have hdep : triStageNT gs c r0 ℓ (Function.update ω j x') j = triStageNT gs c r0 ℓ ω j :=
        triStageNT_dep gs c r0 ℓ _ _ j fun i hi => Function.update_of_ne (ne_of_lt hi) _ _
      simp only [C, Set.mem_ofPred_eq, Function.update_idem, hdep]
    · intro ω
      set P := triStageNT gs c r0 ℓ ω j with hPdef
      by_cases hg : TriStageGood K c r0 j P
      · -- on the good event of the earlier stages: (SEP0) holds, the core applies
        have hP0 : j = 0 → P = pgPack c (r0 • 1) := by rintro rfl; rfl
        obtain ⟨hdet, hbody⟩ := triStage_inputK hd K hKc hKcl c r0 hr0 hK0 j P hP0 hg
        have hPq : IsRatPg P := isRatPg_triStageNT gs c hcq r0 hr0q ℓ ω j
        have hsepP := hsep j P hPq hdet hbody
        have hgm : Measurable (gs j P) := (hgs j).comp (measurable_const.prodMk measurable_id)
        refine le_trans (measure_mono ?_) (triCoreStageT d hd _ hbody (gs j P) hgm as cs has0 hcs0 has hτ hsepP
          ℓ δ' hδ'0 hδ'1 hℓ' AdversarialBco.BitRAM.coinStream (fun t x => triDraw d B x t) hy hind hlaw
          (fun t x => hyM x t) fun t x => isRatE_triDraw d B x t)
        intro x hx hgood
        apply hx.2
        have hsj : triStageNT gs c r0 ℓ (Function.update ω j x) j = P :=
          triStageNT_dep gs c r0 ℓ _ _ j fun i hi => Function.update_of_ne (ne_of_lt hi) _ _
        show PgGood d (K ∩ triCube c (2 ^ (j + 1) * r0)) (36.4 * d * pgLam (triRh d))
          (some (triStageNT gs c r0 ℓ (Function.update ω j x) (j + 1)))
        simp only [triStageNT, hsj, Function.update_self]
        exact pgGood_comp d _ _ P _ hdet hgood
      · -- off it the event of stage `j` is empty: the step is never charged there
        have hempty : {x | (ω, x) ∈ C j} = ∅ := by
          ext x
          simp only [C, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hg
        rw [hempty, measure_empty]
        exact bot_le
  have hKm : K ∩ triCube c (2 ^ M * r0) = K := by
    refine Set.inter_eq_left.2 fun y hy i => ?_
    have h1 : dist y c ≤ R0 := hKR hy
    have h2 : |y i - c i| ≤ dist y c := by
      rw [dist_eq_norm, ← Real.norm_eq_abs]
      exact PiLp.norm_apply_le (y - c) i
    linarith
  have hfinal : ∀ ω, TriStageGood K c r0 M (triStageNT gs c r0 ℓ ω M) →
      PgGood d K (36.4 * d * pgLam (triRh d)) (some (triStageNT gs c r0 ℓ ω M)) := by
    intro ω hω
    obtain ⟨k, hk⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    rw [hk] at hω ⊢
    rw [hk] at hKm
    simpa only [TriStageGood, hKm] using hω
  have hcover : {ω | ¬ PgGood d K (36.4 * d * pgLam (triRh d)) (some (triStageNT gs c r0 ℓ ω M))} ⊆
      ⋃ j ∈ Finset.range M, {ω | (ω, ω j) ∈ C j} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Finset.mem_range, not_exists] at hnot
    have hall : ∀ i ≤ M, TriStageGood K c r0 i (triStageNT gs c r0 ℓ ω i) := by
      intro i hi
      induction i with
      | zero => trivial
      | succ i ih =>
        by_contra hb
        refine hnot i (by omega) ?_
        refine ⟨ih (by omega), ?_⟩
        simpa only [Function.update_eq_self] using hb
    exact hω (hfinal ω (hall _ le_rfl))
  calc (Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream)
        {ω | ¬ PgGood d K (36.4 * d * pgLam (triRh d)) (some (triStageNT gs c r0 ℓ ω M))}
      ≤ (Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream)
          (⋃ j ∈ Finset.range M, {ω | (ω, ω j) ∈ C j}) := measure_mono hcover
    _ ≤ ∑ j ∈ Finset.range M, (Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream)
          {ω | (ω, ω j) ∈ C j} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range M, ENNReal.ofReal δ' := Finset.sum_le_sum fun j _ => hE j
    _ = ENNReal.ofReal δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hδ']
        field_simp

/-! ## The coins of the procedure -/

theorem triPosT_meas (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgs : ∀ j, Measurable fun q : PgSp d × EuclideanSpace ℝ (Fin d) => gs j q.1 q.2)
    (c : EuclideanSpace ℝ (Fin d)) (r0 R0 : ℝ) (ℓ : ℕ) : Measurable (triPosT gs c r0 R0 ℓ) := by
  have hΦ : Measurable fun cs : ℕ → Bool => fun j k => cs (triLay (triMst r0 R0) (triLT d ℓ) (j, k)) :=
    Measurable.of_eval fun j => Measurable.of_eval fun k => measurable_pi_apply _
  exact (triStageNT_meas gs hgs c r0 ℓ _).comp hΦ

/-- **Theorem TRI-OGD-O** on the coin stream: on the frame `B̄(c, r0) ⊆ K ⊆ B̄(c, R0)` with `c`, `r0` rational, a
program field `gs` measurable in `(P, z)` and satisfying `PosSepHyp` with `0 ≤ as ≤ 1/64`, `0 ≤ cs`,
`16 (as (1 + M_d) Δ + cs) ≤ e_lo`, and an integer `ℓ ≥ log(m_st/δ)`, the position returned is good for `K` at the
radius `36.4 d λ(ρ_h)` outside an event of probability `δ`. -/
theorem triPosT_bad (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (c : EuclideanSpace ℝ (Fin d)) (hcq : IsRatE c) (r0 R0 : ℝ) (hr0q : IsQ r0) (hr0 : 0 < r0)
    (hK0 : Metric.closedBall c r0 ⊆ K) (hKR : K ⊆ Metric.closedBall c R0)
    (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgs : ∀ j, Measurable fun q : PgSp d × EuclideanSpace ℝ (Fin d) => gs j q.1 q.2)
    (as cs : ℝ) (has0 : 0 ≤ as) (hcs0 : 0 ≤ cs) (has : as ≤ 1 / 64)
    (hτ : 16 * (as * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d)) + cs) ≤ triElo d)
    (hsep : PosSepHyp K c r0 gs as cs) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ℓ : ℕ) (hℓ : Real.log (triMst r0 R0 / δ) ≤ ℓ) :
    AdversarialBco.BitRAM.coinStream {cs' | ¬ PgGood d K (36.4 * d * pgLam (triRh d))
      (some (triPosT gs c r0 R0 ℓ cs'))} ≤ ENNReal.ofReal δ := by
  set Φ : (ℕ → Bool) → ℕ → ℕ → Bool := fun cs' j k => cs' (triLay (triMst r0 R0) (triLT d ℓ) (j, k)) with hΦdef
  have hΦ : Measurable Φ :=
    Measurable.of_eval fun j => Measurable.of_eval fun k => measurable_pi_apply _
  have hlaw : AdversarialBco.BitRAM.coinStream.map Φ =
      Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream :=
    coin_curry_inj AdversarialBco.BitRAM.coinLaw _ (tri_lay_inj (triMst r0 R0) (triLT d ℓ))
  set S := {ω : ℕ → ℕ → Bool | ¬ PgGood d K (36.4 * d * pgLam (triRh d))
    (some (triStageNT gs c r0 ℓ ω (triMst r0 R0)))} with hSdef
  have hS : MeasurableSet S :=
    (PgMeas.pgGoodMeas d K _ hKc hKcl).compl.preimage (triStageNT_meas gs hgs c r0 ℓ _)
  calc AdversarialBco.BitRAM.coinStream {cs' | ¬ PgGood d K (36.4 * d * pgLam (triRh d))
        (some (triPosT gs c r0 R0 ℓ cs'))} = AdversarialBco.BitRAM.coinStream (Φ ⁻¹' S) := rfl
    _ = (AdversarialBco.BitRAM.coinStream.map Φ) S := (Measure.map_apply hΦ hS).symm
    _ ≤ ENNReal.ofReal δ := by
      rw [hlaw]
      exact triStagesT hd K hKc hKcl c hcq r0 R0 hr0q hr0 hK0 hKR gs hgs as cs has0 hcs0 has hτ hsep δ hδ0 hδ1 ℓ hℓ

/-! ## The measurability of a field read on rational points -/

/-- A function that vanishes off a countable set is measurable. -/
theorem upos_measurable_of_countable {X Y : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [Zero Y] (f : X → Y) (S : Set X) (hS : S.Countable) (hf : ∀ x ∉ S, f x = 0) :
    Measurable f := by
  intro B _
  have h1 : MeasurableSet (f ⁻¹' B ∩ S) := (hS.mono Set.inter_subset_right).measurableSet
  have h2 : MeasurableSet (f ⁻¹' B ∩ Sᶜ) := by
    by_cases h0 : (0 : Y) ∈ B
    · have : f ⁻¹' B ∩ Sᶜ = Sᶜ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, and_iff_right_iff_imp]
        intro hx; rw [hf x hx]; exact h0
      rw [this]; exact hS.measurableSet.compl
    · have : f ⁻¹' B ∩ Sᶜ = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro hfx hx; rw [hf x hx] at hfx; exact h0 hfx
      rw [this]; exact MeasurableSet.empty
  have e : f ⁻¹' B = (f ⁻¹' B ∩ S) ∪ (f ⁻¹' B ∩ Sᶜ) := (Set.inter_union_compl _ _).symm
  rw [e]
  exact h1.union h2

/-- The rational points of `PgSp d × ℝ^d` form a countable set. -/
theorem upos_countable_ratPt :
    {q : PgSp d × EuclideanSpace ℝ (Fin d) | IsRatPg q.1 ∧ IsRatE q.2}.Countable := by
  classical
  let F : ((Fin d ⊕ Fin d × Fin d) → ℚ) × (Fin d → ℚ) → PgSp d × EuclideanSpace ℝ (Fin d) :=
    fun p => (WithLp.toLp 2 fun k => (p.1 k : ℝ), WithLp.toLp 2 fun i => (p.2 i : ℝ))
  refine (Set.countable_range F).mono ?_
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  refine ⟨(fun k => (hx k).choose, fun i => (hz i).choose), ?_⟩
  simp only [F, Prod.mk.injEq]
  constructor
  · ext k; exact (hx k).choose_spec
  · ext i; exact (hz i).choose_spec

end AdversarialBco.UniPos
