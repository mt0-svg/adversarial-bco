/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgRunMeas
public import AdversarialBco.UW.ProgRec
public import AdversarialBco.Unified.AsmMeasRec

@[expose] public section

/-!
# (O4-M) for BL-OW's record

`measRecUW : MeasRecUW (implW P C' k)`, Unified/AsmMeasRec.lean with BL-O's run replaced by BL-OW's
(UW/ProgRunMeas.lean) and P° of Theorem U by P° of Theorem UW at PARAM-W's reference (`poW`, the level
`δ_c = deltaC d n k_δ`):

* the shift and the advice of a round `t < n` at fixed discrete data (`shGOW`, `advGOW`; `shOW_eqG`, `advOW_eqG`) are
  measurable in the loss parameter, the world's draw, noise and coupling coordinates and P°'s mode (`shGOW_meas`,
  `advGOW_meas`); the advice reads P°'s observation through the weight and the clip, `obsW`, which is continuous
  (`obsW_meas`);
* P°'s gauge is continuous at every position, in every case: the body `kTh n δ K q` reads the level `δ` only through
  `R = 134 d (ln(2d + 2))^{1/2} ≥ 1` (`gauge_kThW_meas`), so `MeasRecUW` needs no case;
* the discrete data are functions of the coins below `D' t` (`D (t + 1)`) and of the readings of the rounds `< t`
  (`< t + 1`), adapted by `readsW_meas`; `measurable_param` concludes.
-/

open MeasureTheory
open scoped Matrix

namespace AdversarialBco.UW.BLOW

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified (NoisyAdv envWorld)
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

/-- The shift of a round in which BL-O is in mode `run st` and P° in mode `run so` (the first branch of `shOW`), at
BL-OW's configuration `c`, position `q`, draw `ξ'` and play `x'`, the loss parameter `l`, the world's draw `ξ` and noise
`e`. -/
noncomputable def shRunOW (c : CfgO d) (q : PgSp d) (st : St d) (ξ' x' : Fin d → ℚ) (so : Df2St d) (l : Λ)
    (ξ : Fin d → ℝ) (e : ℝ) : ℝ × ℝ :=
  let Xo := refX (poW d n δ) so ξ
  let pto := refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) Xo
  let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
  let pt' : ℝ := ptO orc c (XO c st ξ')
  let r := pt' / pto
  ((r - 1) * e + (pt' * fL K L t l (toE x') - pto * fL K L t l xo + 4 * (pt' - 1) / (c.par.eps : ℝ) -
      4 * (pto - 1) / (poW d n δ).eps) / pto, r)

/-- The shift at fixed discrete data and BL-OW's mode `md`, as a function of P°'s mode `mo`. -/
noncomputable def shGOW (c : CfgO d) (q : PgSp d) (md : Mode d) (ξ' x' : Fin d → ℚ) (mo : Df2Mode d) (l : Λ)
    (ξ : Fin d → ℝ) (e : ℝ) : ℝ × ℝ :=
  match mo, md with
  | .run so, .run st => shRunOW L n δ K orc t c q st ξ' x' so l ξ e
  | _, _ => (0, 1)

/-- P°'s observation at fixed discrete data (`refYOW`). -/
noncomputable def refYGOW (c : CfgO d) (q : PgSp d) (md : Mode d) (ξ' x' : Fin d → ℚ) (so : Df2St d) (l : Λ)
    (ξ : Fin d → ℝ) (e : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  let Xo := refX (poW d n δ) so ξ
  let pto := refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) Xo
  let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
  let sh := shGOW L n δ K orc t c q md ξ' x' (.run so) l ξ e
  pto * (fL K L t l xo + e + coupMax sh.1 sh.2 z) / 2 + 2 * (pto - 1) / (poW d n δ).eps

/-- The advice at fixed discrete data (BL-OW's draw `dr`, play `x'` and reading `obs`), as a function of P°'s mode. -/
noncomputable def advGOW (c : CfgO d) (q : PgSp d) (md : Mode d) (dr : (Fin d → ℚ) × ℚ) (x' : Fin d → ℚ) (obs : ℤ)
    (mo : Df2Mode d) (l : Λ) (ξ : Fin d → ℝ) (e : ℝ) (z : Fin 3 → ℝ) : Adv d :=
  match mo, md with
  | .run so, .run st =>
    advQOW (b0OW d n δ) (y0OW d n δ) orc c n st dr.1 dr.2 obs (poW d n δ) so ξ
      (refYGOW L n δ K orc t c q md dr.1 x' so l ξ e z)
  | _, _ => (0, 0)

end Gen

/-! ## Measurability at fixed discrete data -/

/-- The weighted observation is continuous in `(ξ, Y)`. -/
theorem obsW_meas (b0 y0 : ℝ) : Measurable fun x : (Fin d → ℝ) × ℝ => obsW b0 y0 x.1 x.2 := by
  have h1 : Continuous fun x : (Fin d → ℝ) × ℝ => x.1 ⬝ᵥ x.1 := continuous_fst.dotProduct continuous_fst
  have h2 : Continuous fun x : (Fin d → ℝ) × ℝ => wgt b0 (x.1 ⬝ᵥ x.1) :=
    continuous_const.min (continuous_const.max (continuous_const.sub h1))
  have h3 : Continuous fun x : (Fin d → ℝ) × ℝ => clipW y0 x.2 :=
    continuous_const.max (continuous_const.min continuous_snd)
  exact (h2.mul h3).measurable

section GenMeas

variable {n : ℕ} {δ : ℚ} {K : Set (E d)}

/-- `R = 134 d (ln(2d + 2))^{1/2} ≥ 1` at every level. -/
theorem one_le_R (n : ℕ) (δ : ℝ) (hd : 1 ≤ d) : 1 ≤ (df2oPar d n δ).R := by
  show 1 ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * d + 2))
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl : 1 ≤ Real.log (2 * d + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hs : 1 ≤ Real.sqrt (Real.log (2 * d + 2)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hl
  nlinarith

/-- P°'s gauge at any position is continuous, hence measurable: the body reads the level only through `R`. -/
theorem gauge_kThW_meas (hd : 1 ≤ d) (hKc : IsClosed K) (hKv : Convex ℝ K) (q : PgSp d) :
    Measurable (gauge (kTh n (deltaC d n (kDel δ)) K q)) := by
  have hR1 := one_le_R n (deltaC d n (kDel δ)) hd
  have hmw : 1 / (df2oPar d n (deltaC d n (kDel δ))).R ≤ df2Mw d := inv_R_le_df2Mw d hd
  obtain ⟨hconv, -, h1, -⟩ := body_kTh hKc hKv hR1 hmw q
  have hnhds : kTh n (deltaC d n (kDel δ)) K q ∈ nhds (0 : E d) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) h1
  exact (continuous_gauge hconv hnhds).measurable

section Run

variable (hd : 1 ≤ d) (hKc : IsClosed K) (hKv : Convex ℝ K)
include hd hKc hKv

/-- P°'s scale `pt°` is measurable in its state and the draw. -/
theorem refPt_measOW (q : PgSp d) :
    Measurable fun y : Df2St d × (Fin d → ℝ) =>
      refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) (refX (poW d n δ) y.1 y.2) := by
  have hg := gauge_kThW_meas (n := n) (δ := δ) hd hKc hKv q
  have hX := refX_measO (d := d) (poW d n δ)
  have htl : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → E d) := by fun_prop
  have h1 : Measurable fun y : Df2St d × (Fin d → ℝ) =>
      gauge (kTh n (deltaC d n (kDel δ)) K q) (WithLp.toLp 2 (refX (poW d n δ) y.1 y.2)) :=
    hg.comp (htl.comp hX)
  unfold refPt
  exact measurable_const.max (h1.div_const _)

/-- P°'s play point is measurable in its state and the draw. -/
theorem refXo_measOW (q : PgSp d) :
    Measurable fun y : Df2St d × (Fin d → ℝ) =>
      pgMu q + pgOp q (WithLp.toLp 2 ((refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) (refX (poW d n δ) y.1 y.2))⁻¹ •
        refX (poW d n δ) y.1 y.2)) := by
  have hP := refPt_measOW (n := n) (δ := δ) hd hKc hKv q
  have hX := refX_measO (d := d) (poW d n δ)
  have htl : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → E d) := by fun_prop
  have hq : Continuous fun v : E d => pgMu q + pgOp q v := continuous_const.add (pgOp q).continuous
  have hsm : Measurable fun y : Df2St d × (Fin d → ℝ) =>
      (refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) (refX (poW d n δ) y.1 y.2))⁻¹ • refX (poW d n δ) y.1 y.2 :=
    hP.inv.smul hX
  exact hq.measurable.comp (htl.comp hsm)

variable {Λ : Type} [MeasurableSpace Λ] {L : ℕ → Λ → E d → ℝ} (orc : (Fin d → ℚ) → ℕ → Bool) (t : ℕ)
  (hconv : ∀ l, ConvexOn ℝ K (L t l)) (hm : ∀ y ∈ interior K, Measurable fun l => L t l y)
include hconv hm

theorem shRunOW_meas (c : CfgO d) (q : PgSp d) (st : St d) (ξ' x' : Fin d → ℚ) :
    Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ =>
      shRunOW L n δ K orc t c q st ξ' x' y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  have hsel : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ => (y.1, y.2.2.1) := by fun_prop
  have hP : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ =>
      refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) (refX (poW d n δ) y.1 y.2.2.1) := by
    simpa only [Function.comp_def] using (refPt_measOW (n := n) (δ := δ) hd hKc hKv q).comp hsel
  have hxo := (refXo_measOW (n := n) (δ := δ) hd hKc hKv q).comp hsel
  have hfL : Measurable fun p : Λ × E d => fL K L t p.1 p.2 := measurable_fL hconv hm
  have hl : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ => y.2.1 := measurable_fst.comp measurable_snd
  have hLo : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ =>
      fL K L t y.2.1 (pgMu q + pgOp q (WithLp.toLp 2
        ((refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) (refX (poW d n δ) y.1 y.2.2.1))⁻¹ •
          refX (poW d n δ) y.1 y.2.2.1))) := by
    simpa only [Function.comp_def] using hfL.comp (hl.prodMk hxo)
  have hL' : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ => fL K L t y.2.1 (toE x') :=
    hfL.comp (hl.prodMk measurable_const)
  have he : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ => y.2.2.2 := by fun_prop
  unfold shRunOW
  dsimp only
  exact meas_shapeO hP hLo hL' he _ _ _

theorem shGOW_meas (c : CfgO d) (q : PgSp d) (md : Mode d) (ξ' x' : Fin d → ℚ) :
    Measurable fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d =>
      shGOW L n δ K orc t c q md ξ' x' y.2.2.2 y.1 y.2.1 y.2.2.1 := by
  have hcode : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d => y.2.2.2.code :=
    ApMeas.measurable_mode_code.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  cases md with
  | off =>
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d => shGOW L n δ K orc t c q Mode.off ξ' x' y.2.2.2 y.1 y.2.1
        y.2.2.1) = fun _ => ((0 : ℝ), (1 : ℝ)) := by
      funext y; rcases y with ⟨l, ξ, e, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | guard =>
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d => shGOW L n δ K orc t c q Mode.guard ξ' x' y.2.2.2 y.1 y.2.1
        y.2.2.1) = fun _ => ((0 : ℝ), (1 : ℝ)) := by
      funext y; rcases y with ⟨l, ξ, e, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | run st =>
    have hrun := shRunOW_meas (n := n) (δ := δ) hd hKc hKv orc t hconv hm c q st ξ' x'
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d => shGOW L n δ K orc t c q (Mode.run st) ξ' x' y.2.2.2 y.1
        y.2.1 y.2.2.1) = fun y => if y.2.2.2.code.1 = 2 then
          shRunOW L n δ K orc t c q st ξ' x' y.2.2.2.code.2 y.1 y.2.1 y.2.2.1 else ((0 : ℝ), (1 : ℝ)) := by
      funext y; rcases y with ⟨l, ξ, e, mo⟩; cases mo <;> rfl
    rw [h]
    have hsel : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d => (y.2.2.2.code.2, y.1, y.2.1, y.2.2.1) :=
      (measurable_snd.comp hcode).prodMk (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))))
    have hthen : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × Df2Mode d =>
        shRunOW L n δ K orc t c q st ξ' x' y.2.2.2.code.2 y.1 y.2.1 y.2.2.1 := by
      simpa only [Function.comp_def] using hrun.comp hsel
    exact Measurable.ite ((measurable_fst.comp hcode) (measurableSet_singleton 2)) hthen measurable_const

theorem refYGOW_meas (c : CfgO d) (q : PgSp d) (md : Mode d) (ξ' x' : Fin d → ℚ) :
    Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      refYGOW L n δ K orc t c q md ξ' x' y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 := by
  have hsel : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => (y.1, y.2.2.1) := by fun_prop
  have hP : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) (refX (poW d n δ) y.1 y.2.2.1) := by
    simpa only [Function.comp_def] using (refPt_measOW (n := n) (δ := δ) hd hKc hKv q).comp hsel
  have hxo := (refXo_measOW (n := n) (δ := δ) hd hKc hKv q).comp hsel
  have hfL : Measurable fun p : Λ × E d => fL K L t p.1 p.2 := measurable_fL hconv hm
  have hl : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => y.2.1 :=
    measurable_fst.comp measurable_snd
  have hLo : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      fL K L t y.2.1 (pgMu q + pgOp q (WithLp.toLp 2
        ((refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) (refX (poW d n δ) y.1 y.2.2.1))⁻¹ •
          refX (poW d n δ) y.1 y.2.2.1))) := by
    simpa only [Function.comp_def] using hfL.comp (hl.prodMk hxo)
  have hsh0 := shGOW_meas (n := n) (δ := δ) hd hKc hKv orc t hconv hm c q md ξ' x'
  have hsel2 : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      (y.2.1, y.2.2.1, y.2.2.2.1, Df2Mode.run y.1) :=
    hl.prodMk ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
        (ApMeas.meas_run measurable_fst)))
  have hsh : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      shGOW L n δ K orc t c q md ξ' x' (.run y.1) y.2.1 y.2.2.1 y.2.2.2.1 := by
    simpa only [Function.comp_def] using hsh0.comp hsel2
  have hz : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => y.2.2.2.2 := by fun_prop
  have hcm : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      coupMax (shGOW L n δ K orc t c q md ξ' x' (.run y.1) y.2.1 y.2.2.1 y.2.2.2.1).1
        (shGOW L n δ K orc t c q md ξ' x' (.run y.1) y.2.1 y.2.2.1 y.2.2.2.1).2 y.2.2.2.2 := by
    simpa only [Function.comp_def] using MaxCoup.measurable_coupMax.comp (hsh.fst.prodMk (hsh.snd.prodMk hz))
  have he : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => y.2.2.2.1 := by fun_prop
  unfold refYGOW
  exact meas_shapeY hP hLo he hcm _

theorem advRunOW_meas (c : CfgO d) (q : PgSp d) (st : St d) (dr : (Fin d → ℚ) × ℚ) (x' : Fin d → ℚ) (obs : ℤ) :
    Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      advQOW (b0OW d n δ) (y0OW d n δ) orc c n st dr.1 dr.2 obs (poW d n δ) y.1 y.2.2.1
        (refYGOW L n δ K orc t c q (.run st) dr.1 x' y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2) := by
  unfold advQOW
  refine Measurable.prodMk ?_ measurable_const
  cases htq : testOW (b0OW d n δ) (y0OW d n δ) orc c st dr.1 dr.2 obs with
  | none => exact measurable_const
  | some pf =>
    obtain ⟨pq, fire⟩ := pf
    have hY := refYGOW_meas (n := n) (δ := δ) hd hKc hKv orc t hconv hm c q (.run st) dr.1 x'
    have hξ : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => y.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have hYw : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
        obsW (b0OW d n δ : ℝ) (y0OW d n δ : ℝ) y.2.2.1
          (refYGOW L n δ K orc t c q (.run st) dr.1 x' y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2) := by
      simpa only [Function.comp_def] using (obsW_meas (d := d) _ _).comp (hξ.prodMk hY)
    have hRT : Measurable fun y : Df2St d × Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
        refTest (poW d n δ) y.1 y.2.2.1 (obsW (b0OW d n δ : ℝ) (y0OW d n δ : ℝ) y.2.2.1
          (refYGOW L n δ K orc t c q (.run st) dr.1 x' y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2)) := by
      simpa only [Function.comp_def] using
        (refTest_meas (poW d n δ)).comp (measurable_fst.prodMk (hξ.prodMk hYw))
    exact selT_meas hRT.fst hRT.snd.fst hRT.snd.snd (ApMeas.measurable_st_ctr.comp measurable_fst)
      (ApMeas.measurable_st_r.comp measurable_fst) _ _ _

theorem advGOW_meas (c : CfgO d) (q : PgSp d) (md : Mode d) (dr : (Fin d → ℚ) × ℚ) (x' : Fin d → ℚ) (obs : ℤ) :
    Measurable fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
      advGOW L n δ K orc t c q md dr x' obs y.2.2.2.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1 := by
  have hcode : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d => y.2.2.2.2.code :=
    ApMeas.measurable_mode_code.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  cases md with
  | off =>
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advGOW L n δ K orc t c q Mode.off dr x' obs y.2.2.2.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1) =
        fun _ => ((0 : Fin d → ℝ), 0) := by
      funext y; rcases y with ⟨l, ξ, e, z, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | guard =>
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advGOW L n δ K orc t c q Mode.guard dr x' obs y.2.2.2.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1) =
        fun _ => ((0 : Fin d → ℝ), 0) := by
      funext y; rcases y with ⟨l, ξ, e, z, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | run st =>
    have hrun := advRunOW_meas (n := n) (δ := δ) hd hKc hKv orc t hconv hm c q st dr x' obs
    have h : (fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advGOW L n δ K orc t c q (Mode.run st) dr x' obs y.2.2.2.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1) =
        fun y => if y.2.2.2.2.code.1 = 2 then
          advQOW (b0OW d n δ) (y0OW d n δ) orc c n st dr.1 dr.2 obs (poW d n δ) y.2.2.2.2.code.2 y.2.1
            (refYGOW L n δ K orc t c q (.run st) dr.1 x' y.2.2.2.2.code.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1)
          else ((0 : Fin d → ℝ), 0) := by
      funext y; rcases y with ⟨l, ξ, e, z, mo⟩; cases mo <;> rfl
    rw [h]
    have hsel : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        (y.2.2.2.2.code.2, y.1, y.2.1, y.2.2.1, y.2.2.2.1) :=
      (measurable_snd.comp hcode).prodMk (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
          (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))))
    have hthen : Measurable fun y : Λ × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advQOW (b0OW d n δ) (y0OW d n δ) orc c n st dr.1 dr.2 obs (poW d n δ) y.2.2.2.2.code.2 y.2.1
          (refYGOW L n δ K orc t c q (.run st) dr.1 x' y.2.2.2.2.code.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1) := by
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
with BL-OW's below `t`. -/
theorem run_congrEW (hδ : 0 < δ) {t N : ℕ} (hN : DO' d n δ r0 R0 a t ≤ N) (p : Ω × (ℕ → ℝ)) {cs' : ℕ → Bool}
    {r' : ℕ → ℤ} (hcs : ∀ j < N, coin p.1 j = cs' j)
    (hr : ∀ i < t, readOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) i = r' i) :
    cfgWW d n δ r0 R0 a (envWorld orc coin loss noise p.1) = cfgOW d n orc δ r0 R0 a cs' ∧
      recPos d n orc coin δ r0 R0 a p = castP (posO d n orc δ r0 R0 a cs') ∧
      modeOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t = trajRW n δ r0 R0 a orc cs' r' t ∧
      (drawO d n δ r0 R0 (coin p.1) t).1 = (drawO d n δ r0 R0 cs' t).1 ∧
      playOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t =
        playPtO orc (cfgOW d n orc δ r0 R0 a cs') (trajRW n δ r0 R0 a orc cs' r' t) (drawO d n δ r0 R0 cs' t).1 := by
  have hK0 : ∀ j < K0O d n δ r0 R0, coin p.1 j = cs' j :=
    fun j hj => hcs j (lt_of_lt_of_le hj (((K0_le_DO (a := a) t).trans (DO_le_DO' t)).trans hN))
  have hpos := (posLocalO d n orc δ r0 R0 a (coin p.1) cs' hδ hK0).2
  have hcfg : cfgWW d n δ r0 R0 a (envWorld orc coin loss noise p.1) = cfgOW d n orc δ r0 R0 a cs' :=
    cfgOW_congr hδ hK0
  have hm : modeOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t = trajRW n δ r0 R0 a orc cs' r' t :=
    (modeOW_eq_trajRW n δ r0 R0 a _ t).trans (trajRW_congr hδ t
      (fun j hj => hcs j (lt_of_lt_of_le hj ((DO_le_DO' t).trans hN))) hr)
  have hdr : (drawO d n δ r0 R0 (coin p.1) t).1 = (drawO d n δ r0 R0 cs' t).1 :=
    (drawLocalO d n δ r0 R0 a (coin p.1) cs' t).1 fun j _ hj => hcs j (lt_of_lt_of_le hj hN)
  refine ⟨hcfg, ?_, hm, hdr, ?_⟩
  · show castP (posO d n orc δ r0 R0 a (coin p.1)) = _
    rw [hpos]
  · show playPtO orc (cfgWW d n δ r0 R0 a (envWorld orc coin loss noise p.1))
      (modeOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) (drawO d n δ r0 R0 (coin p.1) t).1 = _
    rw [hcfg, hm, hdr]

/-- The shift of a round `t < n` at the discrete data of the run. -/
theorem shOW_eqG (hI : InpU n δ r0 R0 a K orc)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {t : ℕ} (ht : t < n)
    (p : Ω × (ℕ → ℝ)) (mo : Df2Mode d) :
    shOW n δ r0 R0 a orc h hI.convex t p mo =
      shGOW (lossO n δ r0 R0 a h hI.convex).L n δ K orc t (cfgWW d n δ r0 R0 a (envWorld orc coin loss noise p.1))
        (recPos d n orc coin δ r0 R0 a p) (modeOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)
        (drawO d n δ r0 R0 (coin p.1) t).1 (playOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) mo
        ((lossO n δ r0 R0 a h hI.convex).lam t p) ((extO n δ r0 R0 a h).xi t p) ((extO n δ r0 R0 a h).nz t p) := by
  have hint : toE (playOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) ∈ interior K :=
    playIntOW d n δ r0 R0 a K _ hI.hd hI.hr0 hI.convex hI.ball_in hI.orc t
  have hx' : (lossO n δ r0 R0 a h hI.convex).L t ((lossO n δ r0 R0 a h hI.convex).lam t p)
      (toE (playOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)) =
      fL K (lossO n δ r0 R0 a h hI.convex).L t ((lossO n δ r0 R0 a h hI.convex).lam t p)
        (toE (playOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)) := by
    rw [← loss_eq_fL h hI.convex ht p hint]
    show ((if ht' : t < n then (⟨loss t p.1, h.adm t ht' p.1⟩ : AdmL K) else ⟨0, admLoss_zero hI.convex⟩).1 _) = _
    simp only [ht, ↓reduceDIte]
  unfold shOW
  simp only [ht, ↓reduceIte]
  cases mo with
  | run so =>
    cases hm : modeOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t with
    | run st =>
      simp only [shGOW, shRunOW, hx']
    | off => rfl
    | guard => rfl
  | off => rfl
  | guard => rfl

/-- P°'s observation of a round `t < n` at the discrete data of the run. -/
theorem refYOW_eqG (hI : InpU n δ r0 R0 a K orc)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {t : ℕ} (ht : t < n)
    (p : Ω × (ℕ → ℝ)) (so : Df2St d) :
    refYOW n δ r0 R0 a orc h hI.convex t p so =
      refYGOW (lossO n δ r0 R0 a h hI.convex).L n δ K orc t (cfgWW d n δ r0 R0 a (envWorld orc coin loss noise p.1))
        (recPos d n orc coin δ r0 R0 a p) (modeOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)
        (drawO d n δ r0 R0 (coin p.1) t).1 (playOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) so
        ((lossO n δ r0 R0 a h hI.convex).lam t p) ((extO n δ r0 R0 a h).xi t p) ((extO n δ r0 R0 a h).nz t p)
        ((extO n δ r0 R0 a h).zz t p) := by
  unfold refYOW refYGOW
  rw [shOW_eqG hI h ht p]
  simp only [ht, ↓reduceIte]

/-- The advice of a round `t < n` at the discrete data of the run. -/
theorem advOW_eqG (hI : InpU n δ r0 R0 a K orc)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {t : ℕ} (ht : t < n)
    (p : Ω × (ℕ → ℝ)) (mo : Df2Mode d) :
    advOW n δ r0 R0 a orc h hI.convex t p mo =
      advGOW (lossO n δ r0 R0 a h hI.convex).L n δ K orc t (cfgWW d n δ r0 R0 a (envWorld orc coin loss noise p.1))
        (recPos d n orc coin δ r0 R0 a p) (modeOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)
        (drawO d n δ r0 R0 (coin p.1) t) (playOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)
        (readOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) mo
        ((lossO n δ r0 R0 a h hI.convex).lam t p) ((extO n δ r0 R0 a h).xi t p) ((extO n δ r0 R0 a h).nz t p)
        ((extO n δ r0 R0 a h).zz t p) := by
  unfold advOW
  simp only [ht, ↓reduceIte, refYOW_eqG hI h ht p]
  cases mo with
  | run so =>
    cases hm : modeOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t with
    | run st => rfl
    | off => rfl
    | guard => rfl
  | off => rfl
  | guard => rfl

/-- The shift of BL-OW's record is known at `F*_t` and P°'s mode. -/
theorem sh_measOW (hI : InpU n δ r0 R0 a K orc)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (t : ℕ) :
    Measurable[((extO n δ r0 R0 a h).Fσ t).prod inferInstance] fun x : (Ω × (ℕ → ℝ)) × Df2Mode d =>
      shOW n δ r0 R0 a orc h hI.convex t x.1 x.2 := by
  by_cases ht : t < n
  swap
  · have : (fun x : (Ω × (ℕ → ℝ)) × Df2Mode d => shOW n δ r0 R0 a orc h hI.convex t x.1 x.2) =
        fun _ => ((0 : ℝ), (1 : ℝ)) := funext fun x => by unfold shOW; simp only [ht, ↓reduceIte]
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
      ((fun j : Fin N => coin p.1 j), fun i : Fin t => rdOW n δ r0 R0 a orc coin loss noise i p) :=
    Measurable.prodMk ((meas_pi_iff _).mpr fun j => hE.coin_play t ht j j.2)
      ((meas_pi_iff _).mpr fun i => (readsW_meas hI h t ht.le i i.2).mono h𝓕 le_rfl)
  have hxg : Measurable[W.Fσ t] (W.xg t) := Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  have hxi : Measurable[W.Fσ t] (W.xi t) :=
    measurable_pi_of fun c => (measurable_pi_apply (Fin.castSucc c)).comp hxg
  have hnz : Measurable[W.Fσ t] (W.nz t) := Measurable.of_comap_le le_sup_right
  have hlam : Measurable[W.Fσ t] (F.lam t) := (F.lam_meas t ht).mono h𝓕 le_rfl
  have hy : Measurable[(W.Fσ t).prod inferInstance] fun x : (Ω × (ℕ → ℝ)) × Df2Mode d =>
      (F.lam t x.1, W.xi t x.1, W.nz t x.1, x.2) :=
    (hlam.comp hfst).prodMk ((hxi.comp hfst).prodMk ((hnz.comp hfst).prodMk hsnd))
  have heq : (fun x : (Ω × (ℕ → ℝ)) × Df2Mode d => shOW n δ r0 R0 a orc h hI.convex t x.1 x.2) = fun x =>
      (fun (v : (Fin N → Bool) × (Fin t → ℤ)) (x : (Ω × (ℕ → ℝ)) × Df2Mode d) =>
        shGOW F.L n δ K orc t (cfgOW d n orc δ r0 R0 a (extC v.1)) (castP (posO d n orc δ r0 R0 a (extC v.1)))
          (trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) t) (drawO d n δ r0 R0 (extC v.1) t).1
          (playGW n δ r0 R0 a orc t N v) x.2 (F.lam t x.1) (W.xi t x.1) (W.nz t x.1))
        ((fun j : Fin N => coin x.1.1 j), fun i : Fin t => rdOW n δ r0 R0 a orc coin loss noise i x.1) x := by
    funext x
    obtain ⟨e1, e2, e3, e4, e5⟩ := run_congrEW (orc := orc) (loss := loss) (noise := noise) hI.hδ0 (le_refl N) x.1
      (cs' := extC fun j : Fin N => coin x.1.1 j)
      (r' := extZ fun i : Fin t => rdOW n δ r0 R0 a orc coin loss noise i x.1)
      (extC_pre _ N) (extZ_pre (fun i => rdOW n δ r0 R0 a orc coin loss noise i x.1) t)
    rw [shOW_eqG hI h ht x.1 x.2, e1, e2, e3, e4, e5]
    rfl
  rw [heq]
  refine measurable_param (mX := (W.Fσ t).prod inferInstance) (hP0.comp hfst)
    (fun (v : (Fin N → Bool) × (Fin t → ℤ)) (x : (Ω × (ℕ → ℝ)) × Df2Mode d) =>
      shGOW F.L n δ K orc t (cfgOW d n orc δ r0 R0 a (extC v.1)) (castP (posO d n orc δ r0 R0 a (extC v.1)))
        (trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) t) (drawO d n δ r0 R0 (extC v.1) t).1
        (playGW n δ r0 R0 a orc t N v) x.2 (F.lam t x.1) (W.xi t x.1) (W.nz t x.1)) fun v => ?_
  have hG := shGOW_meas (L := F.L) (n := n) (δ := δ) hI.hd hI.compact.isClosed hI.convex orc t
    (fun l => (F.adm t ht l).1) (F.meas t ht) (cfgOW d n orc δ r0 R0 a (extC v.1))
    (castP (posO d n orc δ r0 R0 a (extC v.1))) (trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) t)
    (drawO d n δ r0 R0 (extC v.1) t).1 (playGW n δ r0 R0 a orc t N v)
  simpa only [Function.comp_def] using hG.comp hy

/-- The advice of BL-OW's record is known before round `t + 1`, jointly with P°'s mode. -/
theorem adv_measOW (hI : InpU n δ r0 R0 a K orc)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (t : ℕ) :
    Measurable[((extO n δ r0 R0 a h).𝓕 (t + 1)).prod inferInstance] fun x : (Ω × (ℕ → ℝ)) × Df2Mode d =>
      advOW n δ r0 R0 a orc h hI.convex t x.1 x.2 := by
  by_cases ht : t < n
  swap
  · have : (fun x : (Ω × (ℕ → ℝ)) × Df2Mode d => advOW n δ r0 R0 a orc h hI.convex t x.1 x.2) =
        fun _ => ((0 : Fin d → ℝ), (0 : Fin d → ℝ)) := funext fun x => by unfold advOW; simp only [ht, ↓reduceIte]
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
      ((fun j : Fin N => coin p.1 j), fun i : Fin (t + 1) => rdOW n δ r0 R0 a orc coin loss noise i p) :=
    Measurable.prodMk ((meas_pi_iff _).mpr fun j => hE.coin_adapt (t + 1) ht j j.2)
      ((meas_pi_iff _).mpr fun i => readsW_meas hI h (t + 1) ht i i.2)
  have hxg : Measurable[W.Fσ t] (W.xg t) := Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  have hxi : Measurable[W.𝓕 (t + 1)] (W.xi t) :=
    (measurable_pi_of fun c => (measurable_pi_apply (Fin.castSucc c)).comp hxg).mono (hW.Fσ_le t) le_rfl
  have hlam : Measurable[W.𝓕 (t + 1)] (F.lam t) := (F.lam_meas t ht).mono (W.𝓕.mono (Nat.le_succ t)) le_rfl
  have hy : Measurable[(W.𝓕 (t + 1)).prod inferInstance] fun x : (Ω × (ℕ → ℝ)) × Df2Mode d =>
      (F.lam t x.1, W.xi t x.1, W.nz t x.1, W.zz t x.1, x.2) :=
    (hlam.comp hfst).prodMk ((hxi.comp hfst).prodMk (((hW.meas_nz t).comp hfst).prodMk
      (((hW.meas_zz t).comp hfst).prodMk hsnd)))
  have heq : (fun x : (Ω × (ℕ → ℝ)) × Df2Mode d => advOW n δ r0 R0 a orc h hI.convex t x.1 x.2) = fun x =>
      (fun (v : (Fin N → Bool) × (Fin (t + 1) → ℤ)) (x : (Ω × (ℕ → ℝ)) × Df2Mode d) =>
        advGOW F.L n δ K orc t (cfgOW d n orc δ r0 R0 a (extC v.1)) (castP (posO d n orc δ r0 R0 a (extC v.1)))
          (trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) t) (drawO d n δ r0 R0 (extC v.1) t)
          (playPtO orc (cfgOW d n orc δ r0 R0 a (extC v.1)) (trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) t)
            (drawO d n δ r0 R0 (extC v.1) t).1) (extZ v.2 t) x.2 (F.lam t x.1) (W.xi t x.1) (W.nz t x.1)
          (W.zz t x.1))
        ((fun j : Fin N => coin x.1.1 j), fun i : Fin (t + 1) => rdOW n δ r0 R0 a orc coin loss noise i x.1) x := by
    funext x
    obtain ⟨e1, e2, e3, -, e5⟩ := run_congrEW (orc := orc) (loss := loss) (noise := noise) hI.hδ0
      (DO'_le_DO_succ t) x.1 (cs' := extC fun j : Fin N => coin x.1.1 j)
      (r' := extZ fun i : Fin (t + 1) => rdOW n δ r0 R0 a orc coin loss noise i x.1)
      (extC_pre _ N) fun i hi => extZ_pre (fun i => rdOW n δ r0 R0 a orc coin loss noise i x.1) (t + 1) i
        (Nat.lt_succ_of_lt hi)
    have e6 : drawO d n δ r0 R0 (coin x.1.1) t = drawO d n δ r0 R0 (extC fun j : Fin N => coin x.1.1 j) t :=
      drawO_congr a t (extC_pre _ N)
    have e7 : readOW d n δ r0 R0 a (envWorld orc coin loss noise x.1.1) t =
        extZ (fun i : Fin (t + 1) => rdOW n δ r0 R0 a orc coin loss noise i x.1) t :=
      extZ_pre (fun i => rdOW n δ r0 R0 a orc coin loss noise i x.1) (t + 1) t (Nat.lt_succ_self t)
    rw [advOW_eqG hI h ht x.1 x.2, e1, e2, e3, e6, e5, e7]
  rw [heq]
  refine measurable_param (mX := (W.𝓕 (t + 1)).prod inferInstance) (hP0.comp hfst)
    (fun (v : (Fin N → Bool) × (Fin (t + 1) → ℤ)) (x : (Ω × (ℕ → ℝ)) × Df2Mode d) =>
      advGOW F.L n δ K orc t (cfgOW d n orc δ r0 R0 a (extC v.1)) (castP (posO d n orc δ r0 R0 a (extC v.1)))
        (trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) t) (drawO d n δ r0 R0 (extC v.1) t)
        (playPtO orc (cfgOW d n orc δ r0 R0 a (extC v.1)) (trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) t)
          (drawO d n δ r0 R0 (extC v.1) t).1) (extZ v.2 t) x.2 (F.lam t x.1) (W.xi t x.1) (W.nz t x.1)
        (W.zz t x.1)) fun v => ?_
  have hG := advGOW_meas (L := F.L) (n := n) (δ := δ) hI.hd hI.compact.isClosed hI.convex orc t
    (fun l => (F.adm t ht l).1) (F.meas t ht) (cfgOW d n orc δ r0 R0 a (extC v.1))
    (castP (posO d n orc δ r0 R0 a (extC v.1))) (trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) t)
    (drawO d n δ r0 R0 (extC v.1) t)
    (playPtO orc (cfgOW d n orc δ r0 R0 a (extC v.1)) (trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) t)
      (drawO d n δ r0 R0 (extC v.1) t).1) (extZ v.2 t)
  simpa only [Function.comp_def] using hG.comp hy

end Rec

/-- **(O4-M) for BL-OW's record.** -/
theorem measRecUW (P : List BitRAMO.InstrO) (C' : ℝ) (k : ℕ) : MeasRecUW (implW P C' k) := by
  intro d n δ r0 R0 a K orc hI _ Ω _ μ coin loss noise h
  exact ⟨fun t => sh_measOW hI h t, fun t => adv_measOW hI h t⟩

end AdversarialBco.UW.BLOW
