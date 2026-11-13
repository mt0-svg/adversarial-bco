/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLEngine
public import AdversarialBco.Bit.ShadowMeas
public import AdversarialBco.Poly.Df2ApMeasProof

@[expose] public section

/-!
# (O4-M) for BL's record

`blMeas_of`: the shift and the advice of BL's record are measurable (`BLMeas`). Round `t`'s shift is a function of
BL's run before round `t` and of its position (both read the coins before round `t`'s first block, a finite prefix
known at `cσ d t`), of BL's draw `ξ'_t` (known from the draw group, `MeasDrawB`), and, continuously or piecewise
continuously, of the world's draw, the noise and P°'s mode (`shG`, `shG_meas`). The advice of round `t` is a function of
the coins before round `t + 1`'s first block, and of the world's draw, noise and coupling coordinates of round `t` and
P°'s mode (`advG`, `advG_meas`). A function of a countable measurable parameter and the point, measurable in the point
at each value, is measurable (`measurable_param`).
-/

open MeasureTheory
open scoped Matrix

namespace AdversarialBco.Bit.BLP

open AdversarialBco.BitRAM
open AdversarialBco.RealRAM (Strategy lossAd polytope)
open AdversarialBco.Poly
open AdversarialBco.Poly.Layer2 (kTh WΩ rowHyp_of row_one_le_R inv_R_le_df2Mw body_kTh)
open AdversarialBco.Poly.Conj1 (fL)
open AdversarialBco.Bit.Cpl
open AdversarialBco.Bit.Asm

variable {d : ℕ}

/-! ## Countable parameters and coin prefixes -/

/-- A function of a measurable parameter with countably many values and of the point, measurable in the point at each
value of the parameter, is measurable. -/
theorem measurable_param {X Y V : Type*} {mX : MeasurableSpace X} [MeasurableSpace Y] [MeasurableSpace V]
    [Countable V] [MeasurableSingletonClass V] {P : X → V} (hP : Measurable P) (g : V → X → Y)
    (hg : ∀ v, Measurable (g v)) : Measurable fun x => g (P x) x := by
  have h : Measurable fun p : X × V => g p.2 p.1 := measurable_from_prod_countable_left hg
  exact h.comp (measurable_id.prodMk hP)

/-- The coin sequence of a prefix, `false` past it. -/
def extC {N : ℕ} (c : Fin N → Bool) : ℕ → Bool := fun j => if h : j < N then c ⟨j, h⟩ else false

theorem extC_pre (cs : ℕ → Bool) (N : ℕ) : ∀ j < N, cs j = extC (fun j : Fin N => cs j) j :=
  fun j hj => by simp [extC, hj]

/-- The prefix of BL's coins before the first block of round `t` is known at `cσ d t`. -/
theorem meas_pre (R : Routines) (d n t N : ℕ) (hN : N ≤ Sched.blkStart d (R.K0 d n) (par d n).B t 0) :
    Measurable[cσ d t] fun ω : WΩ => fun j : Fin N => betaR R d n ω.1 j :=
  (@measurable_pi_iff WΩ (Fin N) (fun _ => Bool) (cσ d t) _ _).mpr fun j =>
    Sched.meas_beta_c d _ _ t j (lt_of_lt_of_le j.2 hN)

/-! ## The shift -/

/-- The shift of a round in which BL is in mode `run st` and P° in mode `run so`, from BL's run before the round `T`,
its position `S`, its draw `ξ'`, the world's draw `ξ` and noise `e` (the first branch of `shW`). -/
noncomputable def shRun (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (T : Mode d × HistQ d) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (st : St d) (ξ' : Fin d → ℚ)
    (so : Df2St d) (ξ : Fin d → ℝ) (e : ℝ) : ℝ × ℝ :=
  let cfg := mkCfg d n m A b (R.ctr d n m A b) S
  let q := pgPack (toE S.1) (cM S.2)
  let Xo := refX (po d n) so ξ
  let pto := refPt (po d n) (kTh n (deltaBL d n) (polytope A b) q) Xo
  let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
  let pt' : ℝ := ptQ cfg (XQ cfg st ξ')
  let x' : E d := toE (playPt cfg T.1 ξ')
  let r := pt' / pto
  ((r - 1) * e + (pt' * lossL (polytope A b) n σ t T.2 x' -
      pto * (if t < n then fL (polytope A b) (lossL (polytope A b) n σ) t T.2 else (0 : E d → ℝ)) xo +
      4 * (pt' - 1) / (cfg.par.eps : ℝ) - 4 * (pto - 1) / (po d n).eps) / pto, r)

/-- The shift of round `t` as a function of BL's run before round `t`, its position, its draw, the world's draw and
noise, and P°'s mode. -/
noncomputable def shG (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (T : Mode d × HistQ d) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (ξ' : Fin d → ℚ)
    (ξ : Fin d → ℝ) (e : ℝ) (mo : Df2Mode d) : ℝ × ℝ :=
  match mo, T.1 with
  | .run so, .run st => shRun R d n m A b σ t T S st ξ' so ξ e
  | _, _ => (0, 1)

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {σ : Strategy d}

theorem shW_eq (hR : PosLocal R) (t : ℕ) (ω : WΩ) (mo : Df2Mode d) :
    shW R d n m A b σ t ω mo = shG R d n m A b σ t (traj R d n m A b σ (betaR R d n ω.1) t)
      (R.pos d n m A b (betaR R d n ω.1)) (drawW R d n t ω).1 (ξc d t ω) (ω.2 t) mo := by
  have h1 : lossW R d n m A b σ t ω =
      lossL (polytope A b) n σ t (traj R d n m A b σ (betaR R d n ω.1) t).2 := by
    unfold lossW; rw [lamR_eq R hR]; rfl
  have h2 : lossRW R d n m A b σ t ω = if t < n then fL (polytope A b) (lossL (polytope A b) n σ) t
      (traj R d n m A b σ (betaR R d n ω.1) t).2 else 0 := by
    unfold lossRW; rw [lamR_eq R hR]; rfl
  unfold shW shG
  simp only [h1, h2]
  rfl

section Meas

variable (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n)
include hd hn hc

/-- The gauge of P°'s body at any position is measurable (it is continuous, `B̄(0, 1) ⊆ K~`). -/
theorem gauge_kTh_meas (q : PgSp d) : Measurable (gauge (kTh n (deltaBL d n) (polytope A b) q)) := by
  have H := rowHyp_of d n (deltaBL d n) hd hn (deltaBL_pos hd hn) (deltaBL_lt_one hd hn) (hc.trans (by norm_num))
  have hR1 := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n (deltaBL d n)).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  obtain ⟨hconv, -, h1, -⟩ := body_kTh (Conj1Poly.isClosed_polytope A b) (Conj1Poly.convex_polytope A b) hR1 hmw q
  have hnhds : kTh n (deltaBL d n) (polytope A b) q ∈ nhds (0 : E d) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) h1
  exact (continuous_gauge hconv hnhds).measurable

omit hd hn hc in
/-- The loss P° reads in round `t` is measurable. -/
theorem lossR_meas (t : ℕ) (l : HistQ d) :
    Measurable (if t < n then fL (polytope A b) (lossL (polytope A b) n σ) t l else (0 : E d → ℝ)) := by
  split_ifs with ht
  · have hadm : AdmLoss (polytope A b) (lossL (polytope A b) n σ t l) := by
      classical
      unfold lossL
      split_ifs with h
      · exact h t ht l
      · exact admLoss_zero A b
    exact Layer2.measurable_piecewise_interior hadm.1
  · exact measurable_const

omit hd hn hc in
theorem refX_meas : Measurable fun y : Df2St d × (Fin d → ℝ) => refX (po d n) y.1 y.2 := by
  unfold refX
  have hmv : Measurable fun y : Df2St d × (Fin d → ℝ) => y.1.A *ᵥ y.2 :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
      ((ApMeas.measurable_st_A.comp measurable_fst).prodMk measurable_snd)
  have hmu : Measurable fun y : Df2St d × (Fin d → ℝ) => y.1.mu := ApMeas.measurable_st_mu.comp measurable_fst
  fun_prop

/-- P°'s scale `pt°` and play point are measurable in its state and the draw. -/
theorem refPt_meas (q : PgSp d) :
    Measurable fun y : Df2St d × (Fin d → ℝ) =>
      refPt (po d n) (kTh n (deltaBL d n) (polytope A b) q) (refX (po d n) y.1 y.2) := by
  have hg := gauge_kTh_meas (A := A) (b := b) hd hn hc q
  have hX := refX_meas (d := d) (n := n)
  have htl : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → E d) := by fun_prop
  have h1 : Measurable fun y : Df2St d × (Fin d → ℝ) =>
      gauge (kTh n (deltaBL d n) (polytope A b) q) (WithLp.toLp 2 (refX (po d n) y.1 y.2)) :=
    hg.comp (htl.comp hX)
  unfold refPt
  exact measurable_const.max (h1.div_const _)

omit hd hn hc in
theorem meas_shape {Y : Type*} [MeasurableSpace Y] {P L e : Y → ℝ} (hP : Measurable P) (hL : Measurable L)
    (he : Measurable e) (c1 c2 c3 c4 : ℝ) :
    Measurable fun y => ((c1 / P y - 1) * e y + (c1 * c2 - P y * L y + c3 - 4 * (P y - 1) / c4) / P y, c1 / P y) := by
  fun_prop

theorem shRun_meas (t : ℕ) (T : Mode d × HistQ d) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (st : St d)
    (ξ' : Fin d → ℚ) :
    Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => shRun R d n m A b σ t T S st ξ' y.1 y.2.1 y.2.2 := by
  have hpt := refPt_meas (A := A) (b := b) hd hn hc (pgPack (toE S.1) (cM S.2))
  have hX := refX_meas (d := d) (n := n)
  have hLR := lossR_meas (A := A) (b := b) (σ := σ) (n := n) t T.2
  have hsel : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => (y.1, y.2.1) := by fun_prop
  have hP : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      refPt (po d n) (kTh n (deltaBL d n) (polytope A b) (pgPack (toE S.1) (cM S.2))) (refX (po d n) y.1 y.2.1) := by
    simpa only [Function.comp_def] using hpt.comp hsel
  have hX' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => refX (po d n) y.1 y.2.1 := by
    simpa only [Function.comp_def] using hX.comp hsel
  have htl : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → E d) := by fun_prop
  have hq : Continuous fun v : E d => pgMu (pgPack (toE S.1) (cM S.2)) + pgOp (pgPack (toE S.1) (cM S.2)) v :=
    continuous_const.add (pgOp _).continuous
  have hsm : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      (refPt (po d n) (kTh n (deltaBL d n) (polytope A b) (pgPack (toE S.1) (cM S.2)))
        (refX (po d n) y.1 y.2.1))⁻¹ • refX (po d n) y.1 y.2.1 := by fun_prop
  have hxo : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      (if t < n then fL (polytope A b) (lossL (polytope A b) n σ) t T.2 else (0 : E d → ℝ))
        (pgMu (pgPack (toE S.1) (cM S.2)) + pgOp (pgPack (toE S.1) (cM S.2)) (WithLp.toLp 2
          ((refPt (po d n) (kTh n (deltaBL d n) (polytope A b) (pgPack (toE S.1) (cM S.2)))
            (refX (po d n) y.1 y.2.1))⁻¹ • refX (po d n) y.1 y.2.1))) := by
    simpa only [Function.comp_def] using hLR.comp (hq.measurable.comp (htl.comp hsm))
  unfold shRun
  dsimp only
  exact meas_shape hP hxo (measurable_snd.comp measurable_snd) _ _ _ _

/-- The shift as a function of the world's draw, the noise and P°'s mode, at fixed discrete data. -/
theorem shG_meas (t : ℕ) (T : Mode d × HistQ d) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (ξ' : Fin d → ℚ) :
    Measurable fun y : (Fin d → ℝ) × ℝ × Df2Mode d => shG R d n m A b σ t T S ξ' y.1 y.2.1 y.2.2 := by
  obtain ⟨T1, T2⟩ := T
  have hcode : Measurable fun y : (Fin d → ℝ) × ℝ × Df2Mode d => y.2.2.code :=
    ApMeas.measurable_mode_code.comp (measurable_snd.comp measurable_snd)
  cases T1 with
  | off =>
    have h : (fun y : (Fin d → ℝ) × ℝ × Df2Mode d => shG R d n m A b σ t (Mode.off, T2) S ξ' y.1 y.2.1 y.2.2) =
        fun _ => ((0 : ℝ), (1 : ℝ)) := by
      funext y; rcases y with ⟨ξ, e, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | guard =>
    have h : (fun y : (Fin d → ℝ) × ℝ × Df2Mode d => shG R d n m A b σ t (Mode.guard, T2) S ξ' y.1 y.2.1 y.2.2) =
        fun _ => ((0 : ℝ), (1 : ℝ)) := by
      funext y; rcases y with ⟨ξ, e, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | run st =>
    have hrun := shRun_meas (R := R) (σ := σ) (A := A) (b := b) hd hn hc t (Mode.run st, T2) S st ξ'
    have h : (fun y : (Fin d → ℝ) × ℝ × Df2Mode d => shG R d n m A b σ t (Mode.run st, T2) S ξ' y.1 y.2.1 y.2.2) =
        fun y => if y.2.2.code.1 = 2 then
          shRun R d n m A b σ t (Mode.run st, T2) S st ξ' y.2.2.code.2 y.1 y.2.1 else ((0 : ℝ), (1 : ℝ)) := by
      funext y; rcases y with ⟨ξ, e, mo⟩; cases mo <;> rfl
    rw [h]
    have hsel : Measurable fun y : (Fin d → ℝ) × ℝ × Df2Mode d => (y.2.2.code.2, y.1, y.2.1) :=
      (measurable_snd.comp hcode).prodMk (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hthen : Measurable fun y : (Fin d → ℝ) × ℝ × Df2Mode d =>
        shRun R d n m A b σ t (Mode.run st, T2) S st ξ' y.2.2.code.2 y.1 y.2.1 := by
      simpa only [Function.comp_def] using hrun.comp hsel
    exact Measurable.ite ((measurable_fst.comp hcode) (measurableSet_singleton 2)) hthen measurable_const

/-- The shift of BL's record is known at `F_t` and P°'s mode (the first clause of (O4-M)). -/
theorem sh_meas (hR : PosLocal R) (hD : MeasDrawB) (t : ℕ) :
    Measurable[(Fσ d t).prod inferInstance] fun x : WΩ × Df2Mode d => shW R d n m A b σ t x.1 x.2 := by
  set N := Sched.blkStart d (R.K0 d n) (par d n).B t 0 with hN
  have h1 : Measurable[Fσ d t] fun ω : WΩ => fun j : Fin N => betaR R d n ω.1 j :=
    (meas_pre R d n t N le_rfl).mono (le_sup_left.trans le_sup_left) le_rfl
  have h2 : Measurable[Fσ d t] fun ω : WΩ => (drawW R d n t ω).1 :=
    (hD R d n t).mono (le_sup_right.trans le_sup_left) le_rfl
  have hfst := @measurable_fst WΩ (Df2Mode d) (Fσ d t) inferInstance
  have hP : Measurable[(Fσ d t).prod inferInstance] fun x : WΩ × Df2Mode d =>
      ((fun j : Fin N => betaR R d n x.1.1 j), (drawW R d n t x.1).1) := (h1.prodMk h2).comp hfst
  have hξg : Measurable[Fσ d t] (ξg d t) := Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  have hξ : Measurable[Fσ d t] (ξc d t) :=
    AdversarialBco.Poly.Layer2.measurable_pi_of fun c => (measurable_pi_apply (Fin.castSucc c)).comp hξg
  have he : Measurable[Fσ d t] fun ω : WΩ => ω.2 t := Measurable.of_comap_le le_sup_right
  have hy : Measurable[(Fσ d t).prod inferInstance] fun x : WΩ × Df2Mode d => (ξc d t x.1, x.1.2 t, x.2) :=
    (hξ.comp hfst).prodMk ((he.comp hfst).prodMk (@measurable_snd WΩ (Df2Mode d) (Fσ d t) inferInstance))
  have heq : (fun x : WΩ × Df2Mode d => shW R d n m A b σ t x.1 x.2) = fun x =>
      (fun (v : (Fin N → Bool) × (Fin d → ℚ)) (x : WΩ × Df2Mode d) =>
        shG R d n m A b σ t (traj R d n m A b σ (extC v.1) t) (R.pos d n m A b (extC v.1)) v.2
          (ξc d t x.1) (x.1.2 t) x.2)
        ((fun j : Fin N => betaR R d n x.1.1 j), (drawW R d n t x.1).1) x := by
    funext x
    rw [shW_eq hR]
    dsimp only
    rw [traj_congr R hR d n m A b σ (betaR R d n x.1.1) _ t (extC_pre _ N),
      hR d n m A b (betaR R d n x.1.1) _ fun j hj =>
        extC_pre _ N j (lt_of_lt_of_le hj (K0_le_blkStart d (R.K0 d n) (par d n).B t 0))]
  rw [heq]
  refine measurable_param (mX := (Fσ d t).prod inferInstance) hP
    (fun (v : (Fin N → Bool) × (Fin d → ℚ)) (x : WΩ × Df2Mode d) =>
      shG R d n m A b σ t (traj R d n m A b σ (extC v.1) t) (R.pos d n m A b (extC v.1)) v.2
        (ξc d t x.1) (x.1.2 t) x.2) fun v => ?_
  simpa only [Function.comp_def] using
    (shG_meas hd hn hc t (traj R d n m A b σ (extC v.1) t) (R.pos d n m A b (extC v.1)) v.2).comp hy

end Meas

/-! ## The advice -/

/-- P°'s observation of a round in mode `run so` (the `refYW` of the record), from BL's run before the round `T`, its
position `S` and draw `ξ'`, the world's draw `ξ`, noise `e` and coupling coordinates `z`. -/
noncomputable def refYG (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (T : Mode d × HistQ d) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (ξ' : Fin d → ℚ) (so : Df2St d)
    (ξ : Fin d → ℝ) (e : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  let q := pgPack (toE S.1) (cM S.2)
  let Xo := refX (po d n) so ξ
  let pto := refPt (po d n) (kTh n (deltaBL d n) (polytope A b) q) Xo
  let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
  let sh := shG R d n m A b σ t T S ξ' ξ e (.run so)
  pto * ((if t < n then fL (polytope A b) (lossL (polytope A b) n σ) t T.2 else (0 : E d → ℝ)) xo + e +
    coupMax sh.1 sh.2 z) / 2 + 2 * (pto - 1) / (po d n).eps

/-- The advice of round `t` from BL's mode `md` before the round, its run `T`, position `S`, draw `dr` and reading
`obs`, the world's draw `ξ`, noise `e` and coupling coordinates `z`, and P°'s mode `mo`. -/
noncomputable def advG (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (md : Mode d) (T : Mode d × HistQ d) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ)
    (dr : (Fin d → ℚ) × ℚ) (obs : ℤ) (ξ : Fin d → ℝ) (e : ℝ) (z : Fin 3 → ℝ) (mo : Df2Mode d) : Adv d :=
  match mo, md with
  | .run so, .run st =>
    advQ R.ap (mkCfg d n m A b (R.ctr d n m A b) S) n st dr.1 dr.2 obs (po d n) so ξ
      (refYG R d n m A b σ t T S dr.1 so ξ e z)
  | _, _ => (0, 0)

/-- BL's reading of round `t` on the coins `cs` (`obsW` at `cs = β(ω)`). -/
noncomputable def obsC (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (cs : ℕ → Bool) (t : ℕ) : ℤ :=
  ⌊(2 : ℝ) ^ (par d n).p * lossAd σ 0 (fun i => toE (Function.update (traj R d n m A b σ cs t).2 t
      (play R d n m A b σ cs t) i)) t (toE (play R d n m A b σ cs t))⌋

/-- The advice of round `t` on the coins `cs`, the world `x.1` and P°'s mode `x.2`. -/
noncomputable def advC (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (cs : ℕ → Bool) (x : WΩ × Df2Mode d) : Adv d :=
  advG R d n m A b σ t (modeAt R d n m A b σ cs t) (traj R d n m A b σ cs t) (R.pos d n m A b cs) (drawAt R d n cs t)
    (obsC R d n m A b σ cs t) (ξc d t x.1) (x.1.2 t) (zc d t x.1) x.2

theorem refYW_eqG (hR : PosLocal R) (t : ℕ) (ω : WΩ) (so : Df2St d) :
    refYW R d n m A b σ t ω so = refYG R d n m A b σ t (traj R d n m A b σ (betaR R d n ω.1) t)
      (R.pos d n m A b (betaR R d n ω.1)) (drawW R d n t ω).1 so (ξc d t ω) (ω.2 t) (zc d t ω) := by
  have h2 : lossRW R d n m A b σ t ω = if t < n then fL (polytope A b) (lossL (polytope A b) n σ) t
      (traj R d n m A b σ (betaR R d n ω.1) t).2 else 0 := by
    unfold lossRW; rw [lamR_eq R hR]; rfl
  unfold refYW refYG
  rw [shW_eq hR, h2]
  rfl

theorem advW_eqC (hR : PosLocal R) (t : ℕ) (x : WΩ × Df2Mode d) :
    advW R d n m A b σ t x.1 x.2 = advC R d n m A b σ t (betaR R d n x.1.1) x := by
  obtain ⟨ω, mo⟩ := x
  unfold advW advC advG
  cases mo with
  | run so =>
    cases hW : modeW R d n m A b σ t ω with
    | run st =>
      have hW' : modeAt R d n m A b σ (betaR R d n ω.1) t = .run st := hW
      rw [hW']
      dsimp only
      rw [refYW_eqG hR]
      rfl
    | off =>
      have hW' : modeAt R d n m A b σ (betaR R d n ω.1) t = .off := hW
      rw [hW']
    | guard =>
      have hW' : modeAt R d n m A b σ (betaR R d n ω.1) t = .guard := hW
      rw [hW']
  | off => rfl
  | guard => rfl

theorem advC_congr (hR : PosLocal R) (t : ℕ) (cs cs' : ℕ → Bool)
    (h : ∀ j < Sched.blkStart d (R.K0 d n) (par d n).B (t + 1) 0, cs j = cs' j) :
    advC R d n m A b σ t cs = advC R d n m A b σ t cs' := by
  have hT := traj_congr R hR d n m A b σ cs cs' t
    (fun j hj => h j (lt_of_lt_of_le hj (blkStart_mono _ _ _ (Nat.le_succ t))))
  have hS := hR d n m A b cs cs' (fun j hj => h j (lt_of_lt_of_le hj (K0_le_blkStart _ _ _ _ _)))
  have hD := draw_congr cs cs' _ _ d t h
  have hpl : play R d n m A b σ cs t = play R d n m A b σ cs' t := by
    unfold play modeAt cfgOf drawAt; rw [hS, hT, hD]
  have hob : obsC R d n m A b σ cs t = obsC R d n m A b σ cs' t := by
    unfold obsC; rw [hT, hpl]
  funext x
  unfold advC modeAt drawAt
  rw [hT, hS, hD, hob]

/-! ### Measurability of the matrix operations -/

section MatMeas

variable {Y : Type*} [MeasurableSpace Y]

theorem m_mulVec {M : Y → Matrix (Fin d) (Fin d) ℝ} {v : Y → Fin d → ℝ} (hM : Measurable M) (hv : Measurable v) :
    Measurable fun y => M y *ᵥ v y :=
  (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp (hM.prodMk hv)

theorem m_dot {u v : Y → Fin d → ℝ} (hu : Measurable u) (hv : Measurable v) : Measurable fun y => u y ⬝ᵥ v y :=
  (Continuous.dotProduct continuous_fst continuous_snd).measurable.comp (hu.prodMk hv)

theorem m_vmv {u v : Y → Fin d → ℝ} (hu : Measurable u) (hv : Measurable v) :
    Measurable fun y => Matrix.vecMulVec (u y) (v y) := by
  have h : Continuous fun z : (Fin d → ℝ) × (Fin d → ℝ) => (Matrix.vecMulVec z.1 z.2 : Matrix (Fin d) (Fin d) ℝ) :=
    Continuous.matrix_vecMulVec continuous_fst continuous_snd
  exact h.measurable.comp (hu.prodMk hv)

theorem m_tr {M : Y → Matrix (Fin d) (Fin d) ℝ} (hM : Measurable M) : Measurable fun y => (M y)ᵀ :=
  (continuous_id.matrix_transpose).measurable.comp hM

theorem m_addM {M N : Y → Matrix (Fin d) (Fin d) ℝ} (hM : Measurable M) (hN : Measurable N) :
    Measurable fun y => M y + N y := by
  have : OpensMeasurableSpace (Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (OpensMeasurableSpace ((Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)))
  exact continuous_add.measurable.comp (hM.prodMk hN)

theorem m_smulM {c : Y → ℝ} {M : Y → Matrix (Fin d) (Fin d) ℝ} (hc : Measurable c) (hM : Measurable M) :
    Measurable fun y => c y • M y := by
  have : OpensMeasurableSpace (ℝ × Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (OpensMeasurableSpace (ℝ × (Fin d → Fin d → ℝ)))
  exact (continuous_fst.smul continuous_snd).measurable.comp (hc.prodMk hM)

end MatMeas

/-- `refTest` is measurable in P°'s state, the draw and the observation. -/
theorem refTest_meas (p : Df2OPar) :
    Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => refTest p y.1 y.2.1 y.2.2 := by
  have hA : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.A := ApMeas.measurable_st_A.comp measurable_fst
  have hP : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.P := ApMeas.measurable_st_P.comp measurable_fst
  have hb : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.b := ApMeas.measurable_st_b.comp measurable_fst
  have hk : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.k := ApMeas.measurable_st_k.comp measurable_fst
  have hG : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.G := ApMeas.measurable_st_G.comp measurable_fst
  have hl : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.l := ApMeas.measurable_st_l.comp measurable_fst
  have hmu : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.mu := ApMeas.measurable_st_mu.comp measurable_fst
  have hξ : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.2.1 := measurable_fst.comp measurable_snd
  have hY : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.2.2 := measurable_snd.comp measurable_snd
  have hu := m_mulVec hP (m_mulVec hA hξ)
  have hg : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      (y.2.2 / (1 - p.lam)) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) := (hY.div_const _).smul hu
  have hc : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => p.eta * p.kap * p.lam * p.k0 * y.2.2 :=
    measurable_const.mul hY
  have hPmu := m_mulVec hP hmu
  have hum := m_dot hu hmu
  have hP' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      (1 - p.eta * p.kap * p.lam * p.k0 * y.2.2) • y.1.P + (p.eta * p.kap * p.lam * p.k0 * y.2.2) •
        Matrix.vecMulVec (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) :=
    m_addM (m_smulM (measurable_const.sub hc) hP) (m_smulM hc (m_vmv hu hu))
  have hb' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      y.1.b + (p.eta * p.kap * p.lam * p.k0 * y.2.2) •
        (((y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) ⬝ᵥ y.1.mu) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) - y.1.P *ᵥ y.1.mu) :=
    hb.add (hc.smul ((hum.smul hu).sub hPmu))
  have hk' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      y.1.k + p.eta * p.kap * p.lam * p.k0 * y.2.2 / 2 *
        (((y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) ⬝ᵥ y.1.mu) ^ 2 - y.1.mu ⬝ᵥ (y.1.P *ᵥ y.1.mu)) :=
    hk.add ((hc.div_const 2).mul ((hum.pow_const 2).sub (m_dot hmu hPmu)))
  have hG' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      y.1.G + (y.2.2 / (1 - p.lam)) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) := hG.add hg
  have hl' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      y.1.l + ((y.2.2 / (1 - p.lam)) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1))) ⬝ᵥ y.1.mu := hl.add (m_dot hg hmu)
  have h1 : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      p.eta * (y.1.l + ((y.2.2 / (1 - p.lam)) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1))) ⬝ᵥ y.1.mu) -
        2 * (y.1.k + p.eta * p.kap * p.lam * p.k0 * y.2.2 / 2 *
          (((y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) ⬝ᵥ y.1.mu) ^ 2 - y.1.mu ⬝ᵥ (y.1.P *ᵥ y.1.mu))) :=
    (hl'.const_mul _).sub (hk'.const_mul _)
  have h2 : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      (2 : ℕ) • (y.1.b + (p.eta * p.kap * p.lam * p.k0 * y.2.2) •
        (((y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) ⬝ᵥ y.1.mu) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) - y.1.P *ᵥ y.1.mu)) -
      p.eta • (y.1.G + (y.2.2 / (1 - p.lam)) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1))) :=
    ((continuous_const_smul (2 : ℕ)).measurable.comp hb').sub (hG'.const_smul p.eta)
  exact h1.prodMk (h2.prodMk hP')

open Classical in
/-- The selection of the selection lemma is measurable in the test function and the ball, at fixed threshold, point and
decision. -/
theorem selT_meas {Y : Type*} [MeasurableSpace Y] {κ : Y → ℝ} {h : Y → Fin d → ℝ}
    {P : Y → Matrix (Fin d) (Fin d) ℝ} {c0 : Y → Fin d → ℝ} {r : Y → ℝ} (hκ : Measurable κ) (hh : Measurable h)
    (hP : Measurable P) (hc0 : Measurable c0) (hr : Measurable r) (T : ℝ) (p : Fin d → ℝ) (fire : Bool) :
    Measurable fun y => selT (κ y) (h y) (P y) T (c0 y) (r y) p fire := by
  have hPP := m_addM hP (m_tr hP)
  have hgr : Measurable fun y => h y - (P y + (P y)ᵀ) *ᵥ c0 y := hh.sub (m_mulVec hPP hc0)
  have hpc : Measurable fun _ : Y => p := measurable_const
  obtain ⟨V, hV⟩ : ∃ V : Y → Fin d → ℝ, V = fun y =>
      if h y - (P y + (P y)ᵀ) *ᵥ c0 y = 0 then (fun i : Fin d => if (i : ℕ) = 0 then (1 : ℝ) else 0)
      else (oNorm (h y - (P y + (P y)ᵀ) *ᵥ c0 y))⁻¹ • (-(h y - (P y + (P y)ᵀ) *ᵥ c0 y)) := ⟨_, rfl⟩
  have hv : Measurable V := by
    rw [hV]
    exact Measurable.ite (hgr (measurableSet_singleton 0)) measurable_const
      ((ApMeas.measurable_oNorm.comp hgr).inv.smul hgr.neg)
  obtain ⟨DV, hDV⟩ : ∃ DV : Y → Fin d → ℝ, DV = fun y => (c0 y + r y • V y) - p := ⟨_, rfl⟩
  have hdv : Measurable DV := by rw [hDV]; exact (hc0.add (hr.smul hv)).sub_const p
  have hFp : Measurable fun y => κ y + h y ⬝ᵥ p - p ⬝ᵥ (P y *ᵥ p) :=
    (hκ.add (m_dot hh hpc)).sub (m_dot hpc (m_mulVec hP hpc))
  obtain ⟨A0, hA0⟩ : ∃ A0 : Y → ℝ, A0 = fun y => κ y + h y ⬝ᵥ p - p ⬝ᵥ (P y *ᵥ p) - T := ⟨_, rfl⟩
  have hα0 : Measurable A0 := by rw [hA0]; exact hFp.sub_const T
  obtain ⟨A1, hA1⟩ : ∃ A1 : Y → ℝ, A1 = fun y => (h y - (P y + (P y)ᵀ) *ᵥ p) ⬝ᵥ DV y := ⟨_, rfl⟩
  have hα1 : Measurable A1 := by rw [hA1]; exact m_dot (hh.sub (m_mulVec hPP hpc)) hdv
  obtain ⟨A2, hA2⟩ : ∃ A2 : Y → ℝ, A2 = fun y => DV y ⬝ᵥ (P y *ᵥ DV y) := ⟨_, rfl⟩
  have hα2 : Measurable A2 := by rw [hA2]; exact m_dot hdv (m_mulVec hP hdv)
  have hthen : Measurable fun y => p + (2 * A0 y / (Real.sqrt (A1 y ^ 2 + 4 * A0 y * A2 y) - A1 y)) • DV y :=
    hpc.add (((hα0.const_mul 2).div (((hα1.pow_const 2).add ((hα0.const_mul 4).mul hα2)).sqrt.sub
      hα1)).smul hdv)
  have hset : MeasurableSet {y | fire = true ∧ T < κ y + h y ⬝ᵥ p - p ⬝ᵥ (P y *ᵥ p)} :=
    ApMeas.mset_and (MeasurableSet.const _) (ApMeas.mset_lt measurable_const hFp)
  subst hA2 hA1 hA0 hDV hV
  exact Measurable.ite hset hthen measurable_const

section MeasB

variable (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n)
include hd hn hc

omit hd hn hc in
theorem meas_shapeY {Y : Type*} [MeasurableSpace Y] {P L e C : Y → ℝ} (hP : Measurable P) (hL : Measurable L)
    (he : Measurable e) (hC : Measurable C) (c : ℝ) :
    Measurable fun y => P y * (L y + e y + C y) / 2 + 2 * (P y - 1) / c := by
  fun_prop

/-- P°'s observation is measurable in its state, the world's draw, noise and coupling coordinates. -/
theorem refYG_meas (t : ℕ) (T : Mode d × HistQ d) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (ξ' : Fin d → ℚ) :
    Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      refYG R d n m A b σ t T S ξ' y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  have hpt := refPt_meas (A := A) (b := b) hd hn hc (pgPack (toE S.1) (cM S.2))
  have hX := refX_meas (d := d) (n := n)
  have hLR := lossR_meas (A := A) (b := b) (σ := σ) (n := n) t T.2
  have hsel : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => (y.1, y.2.1) := by fun_prop
  have hP : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      refPt (po d n) (kTh n (deltaBL d n) (polytope A b) (pgPack (toE S.1) (cM S.2))) (refX (po d n) y.1 y.2.1) := by
    simpa only [Function.comp_def] using hpt.comp hsel
  have hX' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => refX (po d n) y.1 y.2.1 := by
    simpa only [Function.comp_def] using hX.comp hsel
  have htl : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → E d) := by fun_prop
  have hq : Continuous fun v : E d => pgMu (pgPack (toE S.1) (cM S.2)) + pgOp (pgPack (toE S.1) (cM S.2)) v :=
    continuous_const.add (pgOp _).continuous
  have hsm : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      (refPt (po d n) (kTh n (deltaBL d n) (polytope A b) (pgPack (toE S.1) (cM S.2)))
        (refX (po d n) y.1 y.2.1))⁻¹ • refX (po d n) y.1 y.2.1 := by fun_prop
  have hxo : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      (if t < n then fL (polytope A b) (lossL (polytope A b) n σ) t T.2 else (0 : E d → ℝ))
        (pgMu (pgPack (toE S.1) (cM S.2)) + pgOp (pgPack (toE S.1) (cM S.2)) (WithLp.toLp 2
          ((refPt (po d n) (kTh n (deltaBL d n) (polytope A b) (pgPack (toE S.1) (cM S.2)))
            (refX (po d n) y.1 y.2.1))⁻¹ • refX (po d n) y.1 y.2.1))) := by
    simpa only [Function.comp_def] using hLR.comp (hq.measurable.comp (htl.comp hsm))
  have hsh0 := shG_meas (R := R) (σ := σ) (A := A) (b := b) hd hn hc t T S ξ'
  have hsel2 : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => (y.2.1, y.2.2.1, Df2Mode.run y.1) :=
    (measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk (ApMeas.meas_run measurable_fst))
  have hsh : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      shG R d n m A b σ t T S ξ' y.2.1 y.2.2.1 (.run y.1) := by
    simpa only [Function.comp_def] using hsh0.comp hsel2
  have hcm : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      coupMax (shG R d n m A b σ t T S ξ' y.2.1 y.2.2.1 (.run y.1)).1
        (shG R d n m A b σ t T S ξ' y.2.1 y.2.2.1 (.run y.1)).2 y.2.2.2 := by
    simpa only [Function.comp_def] using MaxCoup.measurable_coupMax.comp
      (hsh.fst.prodMk (hsh.snd.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have he : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) => y.2.2.1 := by fun_prop
  unfold refYG
  exact meas_shapeY hP hxo he hcm _

/-- The advice of a round in which both learners are in mode `run`, measurable in P°'s state, the world's draw,
noise and coupling coordinates. -/
theorem advRun_meas (t : ℕ) (T : Mode d × HistQ d) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (st : St d)
    (dr : (Fin d → ℚ) × ℚ) (obs : ℤ) :
    Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
      advQ R.ap (mkCfg d n m A b (R.ctr d n m A b) S) n st dr.1 dr.2 obs (po d n) y.1 y.2.1
        (refYG R d n m A b σ t T S dr.1 y.1 y.2.1 y.2.2.1 y.2.2.2) := by
  unfold advQ
  refine Measurable.prodMk ?_ measurable_const
  cases htq : testQ R.ap (mkCfg d n m A b (R.ctr d n m A b) S) st dr.1 dr.2 obs with
  | none => exact measurable_const
  | some pf =>
    obtain ⟨pq, fire⟩ := pf
    have hY := refYG_meas (R := R) (σ := σ) (A := A) (b := b) hd hn hc t T S dr.1
    have hRT : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) =>
        refTest (po d n) y.1 y.2.1 (refYG R d n m A b σ t T S dr.1 y.1 y.2.1 y.2.2.1 y.2.2.2) := by
      simpa only [Function.comp_def] using
        (refTest_meas (po d n)).comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hY))
    exact selT_meas hRT.fst hRT.snd.fst hRT.snd.snd (ApMeas.measurable_st_ctr.comp measurable_fst)
      (ApMeas.measurable_st_r.comp measurable_fst) _ _ _

/-- The advice as a function of the world's draw, noise, coupling coordinates and P°'s mode, at fixed discrete
data. -/
theorem advG_meas (t : ℕ) (md : Mode d) (T : Mode d × HistQ d) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ)
    (dr : (Fin d → ℚ) × ℚ) (obs : ℤ) :
    Measurable fun y : (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
      advG R d n m A b σ t md T S dr obs y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  have hcode : Measurable fun y : (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d => y.2.2.2.code :=
    ApMeas.measurable_mode_code.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  cases md with
  | off =>
    have h : (fun y : (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advG R d n m A b σ t Mode.off T S dr obs y.1 y.2.1 y.2.2.1 y.2.2.2) = fun _ => ((0 : Fin d → ℝ), 0) := by
      funext y; rcases y with ⟨ξ, e, z, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | guard =>
    have h : (fun y : (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advG R d n m A b σ t Mode.guard T S dr obs y.1 y.2.1 y.2.2.1 y.2.2.2) = fun _ => ((0 : Fin d → ℝ), 0) := by
      funext y; rcases y with ⟨ξ, e, z, mo⟩; cases mo <;> rfl
    rw [h]; exact measurable_const
  | run st =>
    have hrun := advRun_meas (R := R) (σ := σ) (A := A) (b := b) hd hn hc t T S st dr obs
    have h : (fun y : (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advG R d n m A b σ t (Mode.run st) T S dr obs y.1 y.2.1 y.2.2.1 y.2.2.2) =
        fun y => if y.2.2.2.code.1 = 2 then
          advQ R.ap (mkCfg d n m A b (R.ctr d n m A b) S) n st dr.1 dr.2 obs (po d n) y.2.2.2.code.2 y.1
            (refYG R d n m A b σ t T S dr.1 y.2.2.2.code.2 y.1 y.2.1 y.2.2.1) else ((0 : Fin d → ℝ), 0) := by
      funext y; rcases y with ⟨ξ, e, z, mo⟩; cases mo <;> rfl
    rw [h]
    have hsel : Measurable fun y : (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        (y.2.2.2.code.2, y.1, y.2.1, y.2.2.1) :=
      (measurable_snd.comp hcode).prodMk (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))))
    have hthen : Measurable fun y : (Fin d → ℝ) × ℝ × (Fin 3 → ℝ) × Df2Mode d =>
        advQ R.ap (mkCfg d n m A b (R.ctr d n m A b) S) n st dr.1 dr.2 obs (po d n) y.2.2.2.code.2 y.1
          (refYG R d n m A b σ t T S dr.1 y.2.2.2.code.2 y.1 y.2.1 y.2.2.1) := by
      simpa only [Function.comp_def] using hrun.comp hsel
    exact Measurable.ite ((measurable_fst.comp hcode) (measurableSet_singleton 2)) hthen measurable_const

/-- The advice of BL's record is known at `F_{t+1}` and P°'s mode (the second clause of (O4-M)). -/
theorem adv_meas (hR : PosLocal R) (t : ℕ) :
    Measurable[(cσ d (t + 1)).prod inferInstance] fun x : WΩ × Df2Mode d => advW R d n m A b σ t x.1 x.2 := by
  set N := Sched.blkStart d (R.K0 d n) (par d n).B (t + 1) 0 with hN
  have hfst := @measurable_fst WΩ (Df2Mode d) (cσ d (t + 1)) inferInstance
  have hsnd := @measurable_snd WΩ (Df2Mode d) (cσ d (t + 1)) inferInstance
  have hP : Measurable[(cσ d (t + 1)).prod inferInstance] fun x : WΩ × Df2Mode d =>
      fun j : Fin N => betaR R d n x.1.1 j := (meas_pre R d n (t + 1) N le_rfl).comp hfst
  have hy : Measurable[(cσ d (t + 1)).prod inferInstance] fun x : WΩ × Df2Mode d =>
      (ξc d t x.1, x.1.2 t, zc d t x.1, x.2) :=
    ((meas_ξc t).comp hfst).prodMk (((meas_noise_c t).comp hfst).prodMk (((meas_zc t).comp hfst).prodMk hsnd))
  have heq : (fun x : WΩ × Df2Mode d => advW R d n m A b σ t x.1 x.2) = fun x =>
      (fun (v : Fin N → Bool) (x : WΩ × Df2Mode d) => advC R d n m A b σ t (extC v) x)
        (fun j : Fin N => betaR R d n x.1.1 j) x := by
    funext x
    rw [advW_eqC hR]
    exact congrFun (advC_congr hR t _ _ (extC_pre _ N)) x
  rw [heq]
  refine measurable_param (mX := (cσ d (t + 1)).prod inferInstance) hP
    (fun (v : Fin N → Bool) (x : WΩ × Df2Mode d) => advC R d n m A b σ t (extC v) x) fun v => ?_
  simpa only [Function.comp_def, advC] using (advG_meas hd hn hc t _ _ _ _ _).comp hy

end MeasB

/-- (O4-M) for BL's record: the shift and the advice are measurable (`BLMeas`). -/
theorem blMeas_of (hR : PosLocal R) (hD : MeasDrawB) (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) :
    BLMeas (blRun R d n m A b σ) :=
  ⟨fun t => sh_meas hd hn hc hR hD t, fun t => adv_meas hd hn hc hR t⟩

end AdversarialBco.Bit.BLP
