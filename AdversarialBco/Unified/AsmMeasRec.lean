/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.AsmRunMeas

@[expose] public section

/-!
# (O4-M) for BL-O's record (`MeasRecO`)

`measRecO : MeasRecO`, on the oracle machine on the extension, with the lemmas of Bit/BLRecMeas.lean.

* The shift and the advice of a round `t < n` are written at fixed discrete data (BL-O's configuration, position,
  mode, draw, play and reading) as functions of the loss parameter of round `t`, the world's draw, noise and coupling
  coordinates and P°'s mode (`shGO`, `advGO`; `shO_eqG`, `advO_eqG`); the loss at BL-O's play is `fL` at the play,
  which lies in the interior of `K` (`playIntO`). At fixed discrete data they are measurable (`shGO_meas`,
  `advGO_meas`): `fL` is jointly measurable in the loss parameter and the point (`measurable_fL`), and P°'s gauge is
  continuous in the run case (`gauge_kThO_meas`).
* The discrete data of round `t` are functions of the coins below `D' t` (the shift) or `D (t + 1)` (the advice) and
  of the readings of the rounds `< t` (`< t + 1`) (`run_congr`), which are known at `F*_t` (`ExtOK.coin_play`,
  `reads_meas`) and before round `t + 1` (`ExtOK.coin_adapt`, `reads_meas`); `measurable_param` concludes.
* From round `n` on the shift and the advice are constant.
-/

open MeasureTheory
open scoped Matrix

namespace AdversarialBco.Unified.Asm

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (St Mode extC extC_pre measurable_param refX refPt refTest selT muOf cV refTest_meas
  selT_meas meas_shapeY)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (WorldO)
open AdversarialBco.Poly.Conj1 (fL measurable_fL)
open AdversarialBco.Bit.RQ (castP)

variable {d : ℕ}

/-! ## The shift and the advice at fixed discrete data -/

section Gen

variable {Λ : Type} (L : ℕ → Λ → E d → ℝ) (n : ℕ) (δ : ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
  (t : ℕ)

/-- The shift of a round in which BL-O is in mode `run st` and P° in mode `run so` (the first branch of `shO`), at
BL-O's configuration `c`, position `q`, draw `ξ'` and play `x'`, the loss parameter `l`, the world's draw `ξ` and noise
`e`. -/
noncomputable def shRunO (c : CfgO d) (q : PgSp d) (st : St d) (ξ' x' : Fin d → ℚ) (so : Df2St d) (l : Λ)
    (ξ : Fin d → ℝ) (e : ℝ) : ℝ × ℝ :=
  let Xo := refX (poO d n δ) so ξ
  let pto := refPt (poO d n δ) (kTh n (dBL d n δ) K q) Xo
  let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
  let pt' : ℝ := ptO orc c (XO c st ξ')
  let r := pt' / pto
  ((r - 1) * e + (pt' * fL K L t l (toE x') - pto * fL K L t l xo + 4 * (pt' - 1) / (c.par.eps : ℝ) -
      4 * (pto - 1) / (poO d n δ).eps) / pto, r)

/-- The shift at fixed discrete data and BL-O's mode `md`, as a function of P°'s mode `mo`. -/
noncomputable def shGO (c : CfgO d) (q : PgSp d) (md : Mode d) (ξ' x' : Fin d → ℚ) (mo : Df2Mode d) (l : Λ)
    (ξ : Fin d → ℝ) (e : ℝ) : ℝ × ℝ :=
  match mo, md with
  | .run so, .run st => shRunO L n δ K orc t c q st ξ' x' so l ξ e
  | _, _ => (0, 1)

/-- P°'s observation at fixed discrete data (`refYO`). -/
noncomputable def refYGO (c : CfgO d) (q : PgSp d) (md : Mode d) (ξ' x' : Fin d → ℚ) (so : Df2St d) (l : Λ)
    (ξ : Fin d → ℝ) (e : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  let Xo := refX (poO d n δ) so ξ
  let pto := refPt (poO d n δ) (kTh n (dBL d n δ) K q) Xo
  let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
  let sh := shGO L n δ K orc t c q md ξ' x' (.run so) l ξ e
  pto * (fL K L t l xo + e + coupMax sh.1 sh.2 z) / 2 + 2 * (pto - 1) / (poO d n δ).eps

/-- The advice at fixed discrete data (BL-O's draw `dr`, play `x'` and reading `obs`), as a function of P°'s mode. -/
noncomputable def advGO (c : CfgO d) (q : PgSp d) (md : Mode d) (dr : (Fin d → ℚ) × ℚ) (x' : Fin d → ℚ) (obs : ℤ)
    (mo : Df2Mode d) (l : Λ) (ξ : Fin d → ℝ) (e : ℝ) (z : Fin 3 → ℝ) : Adv d :=
  match mo, md with
  | .run so, .run st =>
    advQO orc c n st dr.1 dr.2 obs (poO d n δ) so ξ (refYGO L n δ K orc t c q md dr.1 x' so l ξ e z)
  | _, _ => (0, 0)

end Gen

/-! ## Measurability at fixed discrete data -/

section GenMeas

variable {n : ℕ} {δ : ℚ} {K : Set (E d)}

/-- P°'s gauge at any position is continuous in the run case, hence measurable. -/
theorem gauge_kThO_meas (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : RunCaseO d n δ)
    (hKc : IsClosed K) (hKv : Convex ℝ K) (q : PgSp d) : Measurable (gauge (kTh n (dBL d n δ) K q)) := by
  obtain ⟨hpos, hlt, -, -, -⟩ := thrO d n δ hd hn hδ0 hδ1
  have H := rowHyp_of d n (dBL d n δ) hd hn hpos hlt (hc.trans (by norm_num))
  have hR1 := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n (dBL d n δ)).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  obtain ⟨hconv, -, h1, -⟩ := body_kTh hKc hKv hR1 hmw q
  have hnhds : kTh n (dBL d n δ) K q ∈ nhds (0 : E d) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) h1
  exact (continuous_gauge hconv hnhds).measurable

theorem refX_measO (P : Df2OPar) : Measurable fun y : Df2St d × (Fin d → ℝ) => refX P y.1 y.2 := by
  unfold refX
  have hmv : Measurable fun y : Df2St d × (Fin d → ℝ) => y.1.A *ᵥ y.2 :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
      ((ApMeas.measurable_st_A.comp measurable_fst).prodMk measurable_snd)
  have hmu : Measurable fun y : Df2St d × (Fin d → ℝ) => y.1.mu := ApMeas.measurable_st_mu.comp measurable_fst
  fun_prop

section Run

variable (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : RunCaseO d n δ) (hKc : IsClosed K)
  (hKv : Convex ℝ K)
include hd hn hδ0 hδ1 hc hKc hKv

/-- P°'s scale `pt°` is measurable in its state and the draw. -/
theorem refPt_measO (q : PgSp d) :
    Measurable fun y : Df2St d × (Fin d → ℝ) =>
      refPt (poO d n δ) (kTh n (dBL d n δ) K q) (refX (poO d n δ) y.1 y.2) := by
  have hg := gauge_kThO_meas hd hn hδ0 hδ1 hc hKc hKv q
  have hX := refX_measO (d := d) (poO d n δ)
  have htl : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → E d) := by fun_prop
  have h1 : Measurable fun y : Df2St d × (Fin d → ℝ) =>
      gauge (kTh n (dBL d n δ) K q) (WithLp.toLp 2 (refX (poO d n δ) y.1 y.2)) :=
    hg.comp (htl.comp hX)
  unfold refPt
  exact measurable_const.max (h1.div_const _)

/-- P°'s play point is measurable in its state and the draw. -/
theorem refXo_measO (q : PgSp d) :
    Measurable fun y : Df2St d × (Fin d → ℝ) =>
      pgMu q + pgOp q (WithLp.toLp 2 ((refPt (poO d n δ) (kTh n (dBL d n δ) K q) (refX (poO d n δ) y.1 y.2))⁻¹ •
        refX (poO d n δ) y.1 y.2)) := by
  have hP := refPt_measO hd hn hδ0 hδ1 hc hKc hKv q
  have hX := refX_measO (d := d) (poO d n δ)
  have htl : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → E d) := by fun_prop
  have hq : Continuous fun v : E d => pgMu q + pgOp q v := continuous_const.add (pgOp q).continuous
  have hsm : Measurable fun y : Df2St d × (Fin d → ℝ) =>
      (refPt (poO d n δ) (kTh n (dBL d n δ) K q) (refX (poO d n δ) y.1 y.2))⁻¹ • refX (poO d n δ) y.1 y.2 :=
    hP.inv.smul hX
  exact hq.measurable.comp (htl.comp hsm)

omit hd hn hδ0 hδ1 hc hKc hKv in
theorem meas_shapeO {Y : Type*} [MeasurableSpace Y] {P L L' e : Y → ℝ} (hP : Measurable P) (hL : Measurable L)
    (hL' : Measurable L') (he : Measurable e) (c1 c3 c4 : ℝ) :
    Measurable fun y => ((c1 / P y - 1) * e y + (c1 * L' y - P y * L y + c3 - 4 * (P y - 1) / c4) / P y,
      c1 / P y) := by
  fun_prop

variable {Λ : Type} [MeasurableSpace Λ] {L : ℕ → Λ → E d → ℝ} (orc : (Fin d → ℚ) → ℕ → Bool) (t : ℕ)
  (hconv : ∀ l, ConvexOn ℝ K (L t l)) (hm : ∀ y ∈ interior K, Measurable fun l => L t l y)
include hconv hm

theorem shRunO_meas (c : CfgO d) (q : PgSp d) (st : St d) (ξ' x' : Fin d → ℚ) :
    Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ =>
      shRunO L n δ K orc t c q st ξ' x' y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  have hsel : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ => (y.1, y.2.2.1) := by fun_prop
  have hP : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ =>
      refPt (poO d n δ) (kTh n (dBL d n δ) K q) (refX (poO d n δ) y.1 y.2.2.1) := by
    simpa only [Function.comp_def] using (refPt_measO hd hn hδ0 hδ1 hc hKc hKv q).comp hsel
  have hxo := (refXo_measO hd hn hδ0 hδ1 hc hKc hKv q).comp hsel
  have hfL : Measurable fun p : Λ × E d => fL K L t p.1 p.2 := measurable_fL hconv hm
  have hl : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ => y.2.1 := measurable_fst.comp measurable_snd
  have hLo : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ =>
      fL K L t y.2.1 (pgMu q + pgOp q (WithLp.toLp 2
        ((refPt (poO d n δ) (kTh n (dBL d n δ) K q) (refX (poO d n δ) y.1 y.2.2.1))⁻¹ •
          refX (poO d n δ) y.1 y.2.2.1))) := by
    simpa only [Function.comp_def] using hfL.comp (hl.prodMk hxo)
  have hL' : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ => fL K L t y.2.1 (toE x') :=
    hfL.comp (hl.prodMk measurable_const)
  have he : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ => y.2.2.2 := by fun_prop
  unfold shRunO
  dsimp only
  exact meas_shapeO hP hLo hL' he _ _ _

theorem shGO_meas (c : CfgO d) (q : PgSp d) (md : Mode d) (ξ' x' : Fin d → ℚ) :
    Measurable fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d =>
      shGO L n δ K orc t c q md ξ' x' y.2.2.2 y.1 y.2.1 y.2.2.1 := by
  have hcode : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d => y.2.2.2.code :=
    ApMeas.measurable_mode_code.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  cases md with
  | off =>
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d => shGO L n δ K orc t c q Mode.off ξ' x' y.2.2.2 y.1 y.2.1
        y.2.2.1) = fun _ => ((0 : ℝ), (1 : ℝ)) := by
      funext y; rcases y with ⟨l, ξ, e, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | guard =>
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d => shGO L n δ K orc t c q Mode.guard ξ' x' y.2.2.2 y.1 y.2.1
        y.2.2.1) = fun _ => ((0 : ℝ), (1 : ℝ)) := by
      funext y; rcases y with ⟨l, ξ, e, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | run st =>
    have hrun := shRunO_meas hd hn hδ0 hδ1 hc hKc hKv orc t hconv hm c q st ξ' x'
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d => shGO L n δ K orc t c q (Mode.run st) ξ' x' y.2.2.2 y.1
        y.2.1 y.2.2.1) = fun y => if y.2.2.2.code.1 = 2 then
          shRunO L n δ K orc t c q st ξ' x' y.2.2.2.code.2 y.1 y.2.1 y.2.2.1 else ((0 : ℝ), (1 : ℝ)) := by
      funext y; rcases y with ⟨l, ξ, e, mo⟩; cases mo <;> rfl
    rw [h]
    have hsel : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d => (y.2.2.2.code.2, y.1, y.2.1, y.2.2.1) :=
      (measurable_snd.comp hcode).prodMk (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))))
    have hthen : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d =>
        shRunO L n δ K orc t c q st ξ' x' y.2.2.2.code.2 y.1 y.2.1 y.2.2.1 := by
      simpa only [Function.comp_def] using hrun.comp hsel
    exact Measurable.ite ((measurable_fst.comp hcode) (measurableSet_singleton 2)) hthen measurable_const

theorem refYGO_meas (c : CfgO d) (q : PgSp d) (md : Mode d) (ξ' x' : Fin d → ℚ) :
    Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      refYGO L n δ K orc t c q md ξ' x' y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 := by
  have hsel : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => (y.1, y.2.2.1) := by fun_prop
  have hP : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      refPt (poO d n δ) (kTh n (dBL d n δ) K q) (refX (poO d n δ) y.1 y.2.2.1) := by
    simpa only [Function.comp_def] using (refPt_measO hd hn hδ0 hδ1 hc hKc hKv q).comp hsel
  have hxo := (refXo_measO hd hn hδ0 hδ1 hc hKc hKv q).comp hsel
  have hfL : Measurable fun p : Λ × E d => fL K L t p.1 p.2 := measurable_fL hconv hm
  have hl : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => y.2.1 :=
    measurable_fst.comp measurable_snd
  have hLo : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      fL K L t y.2.1 (pgMu q + pgOp q (WithLp.toLp 2
        ((refPt (poO d n δ) (kTh n (dBL d n δ) K q) (refX (poO d n δ) y.1 y.2.2.1))⁻¹ •
          refX (poO d n δ) y.1 y.2.2.1))) := by
    simpa only [Function.comp_def] using hfL.comp (hl.prodMk hxo)
  have hsh0 := shGO_meas hd hn hδ0 hδ1 hc hKc hKv orc t hconv hm c q md ξ' x'
  have hsel2 : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      (y.2.1, y.2.2.1, y.2.2.2.1, Df2Mode.run y.1) :=
    hl.prodMk ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
        (ApMeas.meas_run measurable_fst)))
  have hsh : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      shGO L n δ K orc t c q md ξ' x' (.run y.1) y.2.1 y.2.2.1 y.2.2.2.1 := by
    simpa only [Function.comp_def] using hsh0.comp hsel2
  have hz : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => y.2.2.2.2 := by fun_prop
  have hcm : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      coupMax (shGO L n δ K orc t c q md ξ' x' (.run y.1) y.2.1 y.2.2.1 y.2.2.2.1).1
        (shGO L n δ K orc t c q md ξ' x' (.run y.1) y.2.1 y.2.2.1 y.2.2.2.1).2 y.2.2.2.2 := by
    simpa only [Function.comp_def] using MaxCoup.measurable_coupMax.comp (hsh.fst.prodMk (hsh.snd.prodMk hz))
  have he : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => y.2.2.2.1 := by fun_prop
  unfold refYGO
  exact meas_shapeY hP hLo he hcm _

theorem advRunO_meas (c : CfgO d) (q : PgSp d) (st : St d) (dr : (Fin d → ℚ) × ℚ) (x' : Fin d → ℚ) (obs : ℤ) :
    Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      advQO orc c n st dr.1 dr.2 obs (poO d n δ) y.1 y.2.2.1
        (refYGO L n δ K orc t c q (.run st) dr.1 x' y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2) := by
  unfold advQO
  refine Measurable.prodMk ?_ measurable_const
  cases htq : testO orc c st dr.1 dr.2 obs with
  | none => exact measurable_const
  | some pf =>
    obtain ⟨pq, fire⟩ := pf
    have hY := refYGO_meas hd hn hδ0 hδ1 hc hKc hKv orc t hconv hm c q (.run st) dr.1 x'
    have hRT : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
        refTest (poO d n δ) y.1 y.2.2.1
          (refYGO L n δ K orc t c q (.run st) dr.1 x' y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2) := by
      simpa only [Function.comp_def] using
        (refTest_meas (poO d n δ)).comp (measurable_fst.prodMk
          ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk hY))
    exact selT_meas hRT.fst hRT.snd.fst hRT.snd.snd (ApMeas.measurable_st_ctr.comp measurable_fst)
      (ApMeas.measurable_st_r.comp measurable_fst) _ _ _

theorem advGO_meas (c : CfgO d) (q : PgSp d) (md : Mode d) (dr : (Fin d → ℚ) × ℚ) (x' : Fin d → ℚ) (obs : ℤ) :
    Measurable fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
      advGO L n δ K orc t c q md dr x' obs y.2.2.2.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1 := by
  have hcode : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d => y.2.2.2.2.code :=
    ApMeas.measurable_mode_code.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  cases md with
  | off =>
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advGO L n δ K orc t c q Mode.off dr x' obs y.2.2.2.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1) =
        fun _ => ((0 : Fin d → ℝ), 0) := by
      funext y; rcases y with ⟨l, ξ, e, z, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | guard =>
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advGO L n δ K orc t c q Mode.guard dr x' obs y.2.2.2.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1) =
        fun _ => ((0 : Fin d → ℝ), 0) := by
      funext y; rcases y with ⟨l, ξ, e, z, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | run st =>
    have hrun := advRunO_meas hd hn hδ0 hδ1 hc hKc hKv orc t hconv hm c q st dr x' obs
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advGO L n δ K orc t c q (Mode.run st) dr x' obs y.2.2.2.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1) =
        fun y => if y.2.2.2.2.code.1 = 2 then
          advQO orc c n st dr.1 dr.2 obs (poO d n δ) y.2.2.2.2.code.2 y.2.1
            (refYGO L n δ K orc t c q (.run st) dr.1 x' y.2.2.2.2.code.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1)
          else ((0 : Fin d → ℝ), 0) := by
      funext y; rcases y with ⟨l, ξ, e, z, mo⟩; cases mo <;> rfl
    rw [h]
    have hsel : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        (y.2.2.2.2.code.2, y.1, y.2.1, y.2.2.1, y.2.2.2.1) :=
      (measurable_snd.comp hcode).prodMk (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
          (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))))
    have hthen : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advQO orc c n st dr.1 dr.2 obs (poO d n δ) y.2.2.2.2.code.2 y.2.1
          (refYGO L n δ K orc t c q (.run st) dr.1 x' y.2.2.2.2.code.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1) := by
      simpa only [Function.comp_def] using hrun.comp hsel
    exact Measurable.ite ((measurable_fst.comp hcode) (measurableSet_singleton 2)) hthen measurable_const

end Run

end GenMeas


/-! ## The record -/

section Rec

variable {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool}
  {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ}
  {noise : ℕ → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The discrete data of round `t` on coins that agree with the environment's below `N ≥ D' t` and readings that agree
with BL-O's below `t`. -/
theorem run_congrE (hδ : 0 < δ) {t N : ℕ} (hN : DO' d n δ r0 R0 a t ≤ N) (p : Ω × (ℕ → ℝ)) {cs' : ℕ → Bool}
    {r' : ℕ → ℤ} (hcs : ∀ j < N, coin p.1 j = cs' j)
    (hr : ∀ i < t, readO d n δ r0 R0 a (envWorld orc coin loss noise p.1) i = r' i) :
    cfgW d n δ r0 R0 a (envWorld orc coin loss noise p.1) = cfgO d n orc δ r0 R0 a cs' ∧
      recPos d n orc coin δ r0 R0 a p = castP (posO d n orc δ r0 R0 a cs') ∧
      modeO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t = trajR n δ r0 R0 a orc cs' r' t ∧
      (drawO d n δ r0 R0 (coin p.1) t).1 = (drawO d n δ r0 R0 cs' t).1 ∧
      playO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t =
        playPtO orc (cfgO d n orc δ r0 R0 a cs') (trajR n δ r0 R0 a orc cs' r' t) (drawO d n δ r0 R0 cs' t).1 := by
  have hK0 : ∀ j < K0O d n δ r0 R0, coin p.1 j = cs' j :=
    fun j hj => hcs j (lt_of_lt_of_le hj (((K0_le_DO (a := a) t).trans (DO_le_DO' t)).trans hN))
  have hpos := (posLocalO d n orc δ r0 R0 a (coin p.1) cs' hδ hK0).2
  have hcfg : cfgW d n δ r0 R0 a (envWorld orc coin loss noise p.1) = cfgO d n orc δ r0 R0 a cs' :=
    cfgO_congr hδ hK0
  have hm : modeO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t = trajR n δ r0 R0 a orc cs' r' t :=
    (modeO_eq_trajR n δ r0 R0 a _ t).trans (trajR_congr hδ t
      (fun j hj => hcs j (lt_of_lt_of_le hj ((DO_le_DO' t).trans hN))) hr)
  have hdr : (drawO d n δ r0 R0 (coin p.1) t).1 = (drawO d n δ r0 R0 cs' t).1 :=
    (drawLocalO d n δ r0 R0 a (coin p.1) cs' t).1 fun j _ hj => hcs j (lt_of_lt_of_le hj hN)
  refine ⟨hcfg, ?_, hm, hdr, ?_⟩
  · show castP (posO d n orc δ r0 R0 a (coin p.1)) = _
    rw [hpos]
  · show playPtO orc (cfgW d n δ r0 R0 a (envWorld orc coin loss noise p.1))
      (modeO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) (drawO d n δ r0 R0 (coin p.1) t).1 = _
    rw [hcfg, hm, hdr]

/-- The shift of a round `t < n` at the discrete data of the run. -/
theorem shO_eqG (hI : InpU n δ r0 R0 a K orc)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {t : ℕ} (ht : t < n)
    (p : Ω × (ℕ → ℝ)) (mo : Df2Mode d) :
    shO n δ r0 R0 a orc h hI.convex t p mo =
      shGO (lossO n δ r0 R0 a h hI.convex).L n δ K orc t (cfgW d n δ r0 R0 a (envWorld orc coin loss noise p.1))
        (recPos d n orc coin δ r0 R0 a p) (modeO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)
        (drawO d n δ r0 R0 (coin p.1) t).1 (playO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) mo
        ((lossO n δ r0 R0 a h hI.convex).lam t p) ((extO n δ r0 R0 a h).xi t p) ((extO n δ r0 R0 a h).nz t p) := by
  have hint : toE (playO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) ∈ interior K :=
    playIntO d n δ r0 R0 a K _ hI.hd hI.hr0 hI.convex hI.ball_in hI.orc t
  have hx' : (lossO n δ r0 R0 a h hI.convex).L t ((lossO n δ r0 R0 a h hI.convex).lam t p)
      (toE (playO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)) =
      fL K (lossO n δ r0 R0 a h hI.convex).L t ((lossO n δ r0 R0 a h hI.convex).lam t p)
        (toE (playO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)) := by
    rw [← loss_eq_fL h hI.convex ht p hint]
    show ((if ht' : t < n then (⟨loss t p.1, h.adm t ht' p.1⟩ : AdmL K) else ⟨0, admLoss_zero hI.convex⟩).1 _) = _
    simp only [ht, ↓reduceDIte]
  unfold shO
  simp only [ht, ↓reduceIte]
  cases mo with
  | run so =>
    cases hm : modeO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t with
    | run st =>
      simp only [shGO, shRunO, hx']
    | off => rfl
    | guard => rfl
  | off => rfl
  | guard => rfl

/-- P°'s observation of a round `t < n` at the discrete data of the run. -/
theorem refYO_eqG (hI : InpU n δ r0 R0 a K orc)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {t : ℕ} (ht : t < n)
    (p : Ω × (ℕ → ℝ)) (so : Df2St d) :
    refYO n δ r0 R0 a orc h hI.convex t p so =
      refYGO (lossO n δ r0 R0 a h hI.convex).L n δ K orc t (cfgW d n δ r0 R0 a (envWorld orc coin loss noise p.1))
        (recPos d n orc coin δ r0 R0 a p) (modeO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)
        (drawO d n δ r0 R0 (coin p.1) t).1 (playO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) so
        ((lossO n δ r0 R0 a h hI.convex).lam t p) ((extO n δ r0 R0 a h).xi t p) ((extO n δ r0 R0 a h).nz t p)
        ((extO n δ r0 R0 a h).zz t p) := by
  unfold refYO refYGO
  rw [shO_eqG hI h ht p]
  simp only [ht, ↓reduceIte]

/-- The advice of a round `t < n` at the discrete data of the run. -/
theorem advO_eqG (hI : InpU n δ r0 R0 a K orc)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {t : ℕ} (ht : t < n)
    (p : Ω × (ℕ → ℝ)) (mo : Df2Mode d) :
    advO n δ r0 R0 a orc h hI.convex t p mo =
      advGO (lossO n δ r0 R0 a h hI.convex).L n δ K orc t (cfgW d n δ r0 R0 a (envWorld orc coin loss noise p.1))
        (recPos d n orc coin δ r0 R0 a p) (modeO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)
        (drawO d n δ r0 R0 (coin p.1) t) (playO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)
        (readO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) mo
        ((lossO n δ r0 R0 a h hI.convex).lam t p) ((extO n δ r0 R0 a h).xi t p) ((extO n δ r0 R0 a h).nz t p)
        ((extO n δ r0 R0 a h).zz t p) := by
  unfold advO
  simp only [ht, ↓reduceIte, refYO_eqG hI h ht p]
  cases mo with
  | run so =>
    cases hm : modeO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t with
    | run st => rfl
    | off => rfl
    | guard => rfl
  | off => rfl
  | guard => rfl

/-- The shift of BL-O's record is known at `F*_t` and P°'s mode. -/
theorem sh_measO (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (t : ℕ) :
    Measurable[((extO n δ r0 R0 a h).Fσ t).prod inferInstance] fun x : (Ω × (ℕ → ℝ)) × Df2Mode d =>
      shO n δ r0 R0 a orc h hI.convex t x.1 x.2 := by
  by_cases ht : t < n
  swap
  · have : (fun x : (Ω × (ℕ → ℝ)) × Df2Mode d => shO n δ r0 R0 a orc h hI.convex t x.1 x.2) =
        fun _ => ((0 : ℝ), (1 : ℝ)) := funext fun x => by unfold shO; simp only [ht, ↓reduceIte]
    rw [this]
    exact measurable_const
  set W := extO n δ r0 R0 a h with hWdef
  set F := lossO n δ r0 R0 a h hI.convex with hFdef
  have hE := extO_ok n δ r0 R0 a h
  set N := DO' d n δ r0 R0 a t with hN
  have hfst := @measurable_fst (Ω × (ℕ → ℝ)) (Df2Mode d) (W.Fσ t) inferInstance
  have hsnd := @measurable_snd (Ω × (ℕ → ℝ)) (Df2Mode d) (W.Fσ t) inferInstance
  have h𝓕 : W.𝓕 t ≤ W.Fσ t := le_sup_left.trans le_sup_left
  have hP0 : Measurable[W.Fσ t] fun p : Ω × (ℕ → ℝ) =>
      ((fun j : Fin N => coin p.1 j), fun i : Fin t => rdO n δ r0 R0 a orc coin loss noise i p) :=
    Measurable.prodMk ((meas_pi_iff _).mpr fun j => hE.coin_play t ht j j.2)
      ((meas_pi_iff _).mpr fun i => (reads_meas hI h t ht.le i i.2).mono h𝓕 le_rfl)
  have hxg : Measurable[W.Fσ t] (W.xg t) := Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  have hxi : Measurable[W.Fσ t] (W.xi t) :=
    measurable_pi_of fun c => (measurable_pi_apply (Fin.castSucc c)).comp hxg
  have hnz : Measurable[W.Fσ t] (W.nz t) := Measurable.of_comap_le le_sup_right
  have hlam : Measurable[W.Fσ t] (F.lam t) := (F.lam_meas t ht).mono h𝓕 le_rfl
  have hy : Measurable[(W.Fσ t).prod inferInstance] fun x : (Ω × (ℕ → ℝ)) × Df2Mode d =>
      (F.lam t x.1, W.xi t x.1, W.nz t x.1, x.2) :=
    (hlam.comp hfst).prodMk ((hxi.comp hfst).prodMk ((hnz.comp hfst).prodMk hsnd))
  have heq : (fun x : (Ω × (ℕ → ℝ)) × Df2Mode d => shO n δ r0 R0 a orc h hI.convex t x.1 x.2) = fun x =>
      (fun (v : (Fin N → Bool) × (Fin t → ℤ)) (x : (Ω × (ℕ → ℝ)) × Df2Mode d) =>
        shGO F.L n δ K orc t (cfgO d n orc δ r0 R0 a (extC v.1)) (castP (posO d n orc δ r0 R0 a (extC v.1)))
          (trajR n δ r0 R0 a orc (extC v.1) (extZ v.2) t) (drawO d n δ r0 R0 (extC v.1) t).1
          (playG n δ r0 R0 a orc t N v) x.2 (F.lam t x.1) (W.xi t x.1) (W.nz t x.1))
        ((fun j : Fin N => coin x.1.1 j), fun i : Fin t => rdO n δ r0 R0 a orc coin loss noise i x.1) x := by
    funext x
    obtain ⟨e1, e2, e3, e4, e5⟩ := run_congrE (orc := orc) (loss := loss) (noise := noise) hI.hδ0 (le_refl N) x.1
      (cs' := extC fun j : Fin N => coin x.1.1 j)
      (r' := extZ fun i : Fin t => rdO n δ r0 R0 a orc coin loss noise i x.1)
      (extC_pre _ N) (extZ_pre (fun i => rdO n δ r0 R0 a orc coin loss noise i x.1) t)
    rw [shO_eqG hI h ht x.1 x.2, e1, e2, e3, e4, e5]
    rfl
  rw [heq]
  refine measurable_param (mX := (W.Fσ t).prod inferInstance) (hP0.comp hfst)
    (fun (v : (Fin N → Bool) × (Fin t → ℤ)) (x : (Ω × (ℕ → ℝ)) × Df2Mode d) =>
      shGO F.L n δ K orc t (cfgO d n orc δ r0 R0 a (extC v.1)) (castP (posO d n orc δ r0 R0 a (extC v.1)))
        (trajR n δ r0 R0 a orc (extC v.1) (extZ v.2) t) (drawO d n δ r0 R0 (extC v.1) t).1
        (playG n δ r0 R0 a orc t N v) x.2 (F.lam t x.1) (W.xi t x.1) (W.nz t x.1)) fun v => ?_
  have hG := shGO_meas (L := F.L) hI.hd hI.hn hI.hδ0 hI.hδ1 hc hI.compact.isClosed hI.convex orc t
    (fun l => (F.adm t ht l).1) (F.meas t ht) (cfgO d n orc δ r0 R0 a (extC v.1))
    (castP (posO d n orc δ r0 R0 a (extC v.1))) (trajR n δ r0 R0 a orc (extC v.1) (extZ v.2) t)
    (drawO d n δ r0 R0 (extC v.1) t).1 (playG n δ r0 R0 a orc t N v)
  simpa only [Function.comp_def] using hG.comp hy

/-- The advice of BL-O's record is known before round `t + 1`, jointly with P°'s mode. -/
theorem adv_measO (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (t : ℕ) :
    Measurable[((extO n δ r0 R0 a h).𝓕 (t + 1)).prod inferInstance] fun x : (Ω × (ℕ → ℝ)) × Df2Mode d =>
      advO n δ r0 R0 a orc h hI.convex t x.1 x.2 := by
  by_cases ht : t < n
  swap
  · have : (fun x : (Ω × (ℕ → ℝ)) × Df2Mode d => advO n δ r0 R0 a orc h hI.convex t x.1 x.2) =
        fun _ => ((0 : Fin d → ℝ), (0 : Fin d → ℝ)) := funext fun x => by unfold advO; simp only [ht, ↓reduceIte]
    rw [this]
    exact measurable_const
  set W := extO n δ r0 R0 a h with hWdef
  set F := lossO n δ r0 R0 a h hI.convex with hFdef
  have hE := extO_ok n δ r0 R0 a h
  have hW := hE.law
  set N := DO d n δ r0 R0 a (t + 1) with hN
  have hfst := @measurable_fst (Ω × (ℕ → ℝ)) (Df2Mode d) (W.𝓕 (t + 1)) inferInstance
  have hsnd := @measurable_snd (Ω × (ℕ → ℝ)) (Df2Mode d) (W.𝓕 (t + 1)) inferInstance
  have hP0 : Measurable[W.𝓕 (t + 1)] fun p : Ω × (ℕ → ℝ) =>
      ((fun j : Fin N => coin p.1 j), fun i : Fin (t + 1) => rdO n δ r0 R0 a orc coin loss noise i p) :=
    Measurable.prodMk ((meas_pi_iff _).mpr fun j => hE.coin_adapt (t + 1) ht j j.2)
      ((meas_pi_iff _).mpr fun i => reads_meas hI h (t + 1) ht i i.2)
  have hxg : Measurable[W.Fσ t] (W.xg t) := Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  have hxi : Measurable[W.𝓕 (t + 1)] (W.xi t) :=
    (measurable_pi_of fun c => (measurable_pi_apply (Fin.castSucc c)).comp hxg).mono (hW.Fσ_le t) le_rfl
  have hlam : Measurable[W.𝓕 (t + 1)] (F.lam t) := (F.lam_meas t ht).mono (W.𝓕.mono (Nat.le_succ t)) le_rfl
  have hy : Measurable[(W.𝓕 (t + 1)).prod inferInstance] fun x : (Ω × (ℕ → ℝ)) × Df2Mode d =>
      (F.lam t x.1, W.xi t x.1, W.nz t x.1, W.zz t x.1, x.2) :=
    (hlam.comp hfst).prodMk ((hxi.comp hfst).prodMk (((hW.meas_nz t).comp hfst).prodMk
      (((hW.meas_zz t).comp hfst).prodMk hsnd)))
  have heq : (fun x : (Ω × (ℕ → ℝ)) × Df2Mode d => advO n δ r0 R0 a orc h hI.convex t x.1 x.2) = fun x =>
      (fun (v : (Fin N → Bool) × (Fin (t + 1) → ℤ)) (x : (Ω × (ℕ → ℝ)) × Df2Mode d) =>
        advGO F.L n δ K orc t (cfgO d n orc δ r0 R0 a (extC v.1)) (castP (posO d n orc δ r0 R0 a (extC v.1)))
          (trajR n δ r0 R0 a orc (extC v.1) (extZ v.2) t) (drawO d n δ r0 R0 (extC v.1) t)
          (playPtO orc (cfgO d n orc δ r0 R0 a (extC v.1)) (trajR n δ r0 R0 a orc (extC v.1) (extZ v.2) t)
            (drawO d n δ r0 R0 (extC v.1) t).1) (extZ v.2 t) x.2 (F.lam t x.1) (W.xi t x.1) (W.nz t x.1)
          (W.zz t x.1))
        ((fun j : Fin N => coin x.1.1 j), fun i : Fin (t + 1) => rdO n δ r0 R0 a orc coin loss noise i x.1) x := by
    funext x
    obtain ⟨e1, e2, e3, -, e5⟩ := run_congrE (orc := orc) (loss := loss) (noise := noise) hI.hδ0
      (DO'_le_DO_succ t) x.1 (cs' := extC fun j : Fin N => coin x.1.1 j)
      (r' := extZ fun i : Fin (t + 1) => rdO n δ r0 R0 a orc coin loss noise i x.1)
      (extC_pre _ N) fun i hi => extZ_pre (fun i => rdO n δ r0 R0 a orc coin loss noise i x.1) (t + 1) i
        (Nat.lt_succ_of_lt hi)
    have e6 : drawO d n δ r0 R0 (coin x.1.1) t = drawO d n δ r0 R0 (extC fun j : Fin N => coin x.1.1 j) t :=
      drawO_congr a t (extC_pre _ N)
    have e7 : readO d n δ r0 R0 a (envWorld orc coin loss noise x.1.1) t =
        extZ (fun i : Fin (t + 1) => rdO n δ r0 R0 a orc coin loss noise i x.1) t :=
      extZ_pre (fun i => rdO n δ r0 R0 a orc coin loss noise i x.1) (t + 1) t (Nat.lt_succ_self t)
    rw [advO_eqG hI h ht x.1 x.2, e1, e2, e3, e6, e5, e7]
  rw [heq]
  refine measurable_param (mX := (W.𝓕 (t + 1)).prod inferInstance) (hP0.comp hfst)
    (fun (v : (Fin N → Bool) × (Fin (t + 1) → ℤ)) (x : (Ω × (ℕ → ℝ)) × Df2Mode d) =>
      advGO F.L n δ K orc t (cfgO d n orc δ r0 R0 a (extC v.1)) (castP (posO d n orc δ r0 R0 a (extC v.1)))
        (trajR n δ r0 R0 a orc (extC v.1) (extZ v.2) t) (drawO d n δ r0 R0 (extC v.1) t)
        (playPtO orc (cfgO d n orc δ r0 R0 a (extC v.1)) (trajR n δ r0 R0 a orc (extC v.1) (extZ v.2) t)
          (drawO d n δ r0 R0 (extC v.1) t).1) (extZ v.2 t) x.2 (F.lam t x.1) (W.xi t x.1) (W.nz t x.1)
        (W.zz t x.1)) fun v => ?_
  have hG := advGO_meas (L := F.L) hI.hd hI.hn hI.hδ0 hI.hδ1 hc hI.compact.isClosed hI.convex orc t
    (fun l => (F.adm t ht l).1) (F.meas t ht) (cfgO d n orc δ r0 R0 a (extC v.1))
    (castP (posO d n orc δ r0 R0 a (extC v.1))) (trajR n δ r0 R0 a orc (extC v.1) (extZ v.2) t)
    (drawO d n δ r0 R0 (extC v.1) t)
    (playPtO orc (cfgO d n orc δ r0 R0 a (extC v.1)) (trajR n δ r0 R0 a orc (extC v.1) (extZ v.2) t)
      (drawO d n δ r0 R0 (extC v.1) t).1) (extZ v.2 t)
  simpa only [Function.comp_def] using hG.comp hy

end Rec

/-- **(O4-M) for BL-O's record.** -/
theorem measRecO : MeasRecO := by
  intro d n δ r0 R0 a K orc hI hc Ω _ μ coin loss noise h
  exact ⟨fun t => sh_measO hI hc h t, fun t => adv_measO hI hc h t⟩

end AdversarialBco.Unified.Asm
