/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRows
public import AdversarialBco.Bit.BLBasic
public import AdversarialBco.Bit.CoinSchedLaw
public import AdversarialBco.Bit.ShadowWDet
public import AdversarialBco.Bit.ShadowHor
public import AdversarialBco.Bit.ShadowFarm
public import AdversarialBco.Conj1.RunAd
public import AdversarialBco.Bit.BLEngLeaves

@[expose] public section

/-!
# Step 1 of SHADOW for BL's record: `EngineHyp`

The induction `IND(t)` on the good events `Case ∩ Ω_ref ∩ E_bits ∩ Z_n`, over P°'s run:

* `Run.vmode`: from a fresh mode before round `a`, P°'s mode before round `a + s` is the mode of the virtual epoch
  started before `a` (on `Case`);
* `Run.detHyp_of_good`: the five events of the virtual epoch started at `a < n` at the horizon `n - a` give DET's
  hypotheses there;
* `ind`: before every round `t ≤ n` with no decoupled round before it, both learners are in mode `run` on one virtual
  epoch of P° started at a fresh mode, the epoch continued through its rounds `< t - a`, with `Track` between BL's and
  P°'s states (pieces C, `RoundC`, at each step, and the horizon lemma (c), `hor_step`);
* `engine_of`: the shift clause (piece C `PlayC`, Lemma MPAR, the coupling lemma with `κ1 = 0` on `Z_n`) and the regret
  clause
  (E17 with (P4)).
-/

open scoped Matrix

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2
open AdversarialBco.Poly.Conj1 (fL lamAt)

variable {d : ℕ}

namespace Run

variable {n : ℕ} {K : Set (E d)} (B : Run d n K) {δ : ℝ}

/-- On `Case`, from a fresh mode before round `a`, P°'s mode before round `a + s ≤ n` is the mode of the virtual
epoch started before `a`. -/
theorem vmode (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K) {ω : WΩ} (hq : B.Case δ ω) {a : ℕ}
    (hfa : B.mode δ a ω = .run (df2Init (df2oPar d n δ) d)) :
    ∀ s, a + s ≤ n → B.mode δ (a + s) ω = (B.ctx δ a ω).mode (B.path δ a ω) s := by
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have heps0 := eps_pos_of_rows H
  have heps1 : (df2oPar d n δ).eps < 1 := by linarith
  set ρ := B.rr δ ω with hρ
  have hq' : PgGood d ρ.K ρ.p.R (some ρ.q) := hq
  have hbody : Df2Body d ρ.p.R ρ.Kt := body_good hKc hKconv hq'
  obtain ⟨hconv, hclosed, hb1', hbR', -⟩ := hbody
  have h0Kt : (0 : E d) ∈ ρ.Kt := hb1' (Metric.mem_closedBall_self zero_le_one)
  have hK0 : pgMu ρ.q + pgOp ρ.q 0 ∈ ρ.K := h0Kt.1
  have heps0' : 0 < ρ.p.eps := heps0
  have heps1' : ρ.p.eps < 1 := heps1
  have hplayKt : ∀ X : E d, (df2Pip ρ.p ρ.Kt X)⁻¹ • X ∈ ρ.Kt := by
    intro X
    have h := play_mem _ _ hconv hclosed hb1' heps0' heps1' X
    have h2 := hconv.smul_mem_of_zero_mem h0Kt h (t := 1 - ρ.p.eps) ⟨by linarith, by linarith⟩
    rwa [smul_smul, mul_inv_cancel₀ (by linarith : (1 - ρ.p.eps) ≠ 0), one_smul] at h2
  have hplay : ∀ X : Fin d → ℝ, pgMu ρ.q + pgOp ρ.q
      (WithLp.toLp 2 ((df2Pip ρ.p ρ.Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ ρ.K := by
    intro X
    have h := hplayKt (WithLp.toLp 2 X)
    rw [← WithLp.toLp_smul] at h
    exact h.1
  have hfresh := ρ.frm_fresh (ρ.rnd_snd hK0 hplay)
  intro s hs
  rw [mode_rr hKconv hq heps0 heps1 (a + s) hs, RunRec.mode_add, ← mode_rr hKconv hq heps0 heps1 a (by omega),
    hfa]
  have hfr := hfresh a s
  have hc : B.ctx δ a ω = ρ.ctxAt a := by
    unfold Run.ctx RunRec.ctxAt
    rw [kTh_good hq]
    rfl
  refine hfr.trans ?_
  rw [hc]
  refine ctx_mode_congr (ρ.ctxAt a) (ρ.pathAt a) (B.path δ a ω) (n - a) (fun s' hs' => ⟨?_, rfl, rfl⟩) s
    (by omega)
  funext y
  have has : a + s' < n := by omega
  symm
  show gTh n δ K (fun t => B.F.L t (lamAt n B.F.lam a s' ω)) a s' (B.pos ω) y =
    B.F.L (a + s') (B.F.lam (a + s') ω) (pgMu (B.pos ω) + pgOp (B.pos ω) y) / 2
  have hq'' : PgGood d K (df2oPar d n δ).R (some (B.pos ω)) := hq
  simp only [gTh, hq'', ↓reduceIte, lamAt, has]

/-- DET's hypotheses for the virtual epoch started at `a < n`, at the horizon `n - a`, from its five events. -/
theorem detHyp_of_good (hAP : ∀ v : Adv d, ApSpec (apAdv v)) (hreg : Regime d n δ) (hKc : IsClosed K)
    (hKconv : Convex ℝ K) {ω : WΩ} {a : ℕ} (ha : a < n)
    (hev : (B.ctx δ a ω).EvG (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvY (B.path δ a ω) (n - a) ∧
      (B.ctx δ a ω).EvLQ (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvSDF (B.path δ a ω) (n - a) ∧
      (B.ctx δ a ω).EvDQ (B.path δ a ω) (n - a)) :
    DetHyp (B.ctx δ a ω) δ (B.path δ a ω) (n - a) := by
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  obtain ⟨evG, evY, evLQ, evSDF, evDQ⟩ := hev
  exact DetHyp.mk (DetBase.mk (c := B.ctx δ a ω) df2LayerOne_holds lemmaW SIF.df2SIFacts_holds hd hn hδ0 hδ1 rfl
    heps (df2RowsHold d n δ hd hn hδ0 hδ1 heps) (by omega) (Nat.sub_le n a) (body_kTh hKc hKconv hR hmw _)
    (fun s => hAP _) (fun s hs => adm_gTh (f := fun t => B.F.L t (lamAt n B.F.lam a s ω)) (a := a) (s := s)
      hKconv hKc hR hmw (B.F.adm (a + s) (by omega) _) _)) evG evY evLQ evSDF evDQ

/-- On `Case`, P°'s play from the mode `.run so` is the play of its point `X°` at the scale `pt°`, in the interior
of `K`. -/
theorem refPlay_run (hKconv : Convex ℝ K) {ω : WΩ} (hq : B.Case δ ω) (heps0 : 0 < (df2oPar d n δ).eps)
    (heps1 : (df2oPar d n δ).eps < 1) {t : ℕ} {so : Df2St d} (hmo : B.mode δ t ω = .run so) :
    B.refPlay δ t ω = pgMu (B.pos ω) + pgOp (B.pos ω)
      ((BLP.EngL.ptE (kTh n δ K (B.pos ω)) (df2oPar d n δ).eps
          (WithLp.toLp 2 (so.mu + (1 - (df2oPar d n δ).lam) • (so.A *ᵥ ξc d t ω))))⁻¹ •
        WithLp.toLp 2 (so.mu + (1 - (df2oPar d n δ).lam) • (so.A *ᵥ ξc d t ω))) ∧
    B.refPlay δ t ω ∈ interior K := by
  set X : Fin d → ℝ := so.mu + (1 - (df2oPar d n δ).lam) • (so.A *ᵥ ξc d t ω) with hX
  have hint := play_interior hKconv hq heps0 heps1 (WithLp.toLp 2 X)
  have hpt : BLP.EngL.ptE (kTh n δ K (B.pos ω)) (df2oPar d n δ).eps (WithLp.toLp 2 X) =
      df2Pip (df2oPar d n δ) (df2Kp K (B.pos ω) (df2oPar d n δ).R) (WithLp.toLp 2 X) := by
    rw [kTh_good hq]; rfl
  have hval : B.refPlay δ t ω = pgMu (B.pos ω) + pgOp (B.pos ω)
      ((df2Pip (df2oPar d n δ) (df2Kp K (B.pos ω) (df2oPar d n δ).R) (WithLp.toLp 2 X))⁻¹ • WithLp.toLp 2 X) := by
    unfold Run.refPlay cRoundA
    rw [hmo]
    simp only [df2RoundGa]
    rw [kTh_good hq]
    split_ifs with h
    · rw [WithLp.toLp_smul]; rfl
    · exact absurd (by rw [WithLp.toLp_smul]; exact interior_subset hint) h
  rw [hpt]
  exact ⟨hval, hval ▸ hint⟩

end Run

/-- An epoch continued through its rounds `< s` is in mode `run` at its state before round `s`. -/
theorem mode_run_of_cont (c : Df2Ctx d) (π : Df2Path d) :
    ∀ s, (∀ u < s, c.cont π u) → c.mode π s = .run (c.st π s)
  | 0, _ => rfl
  | s + 1, h => by
    obtain ⟨st, hst, -⟩ := h s (Nat.lt_succ_self s)
    simp only [Df2Ctx.st, hst, Df2Mode.stOr]

end AdversarialBco.Bit.Cpl

namespace AdversarialBco.Bit.BLP

open MeasureTheory
open AdversarialBco.BitRAM
open AdversarialBco.RealRAM (Strategy lossAd polytope)
open AdversarialBco.Poly
open AdversarialBco.Poly.Layer2 (kTh WΩ gTh rowHyp_of eps_pos_of_rows row_one_le_R inv_R_le_df2Mw body_kTh kTh_good
  body_good affine_comb)
open AdversarialBco.Poly.Conj1 (fL lamAt)
open AdversarialBco.Bit.Cpl
open AdversarialBco.Bit.Asm
open AdversarialBco.Bit.BLP.EngL (ptE extE)

variable {d : ℕ}

/-! ## The history of the run -/

/-- The history of the run before round `t` holds BL's plays of the rounds `i < t`. -/
theorem traj_hist (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (cs : ℕ → Bool) : ∀ t, ∀ i < t, (traj R d n m A b σ cs t).2 i = play R d n m A b σ cs i
  | 0, i, hi => absurd hi (Nat.not_lt_zero _)
  | t + 1, i, hi => by
    show Function.update (traj R d n m A b σ cs t).2 t
      (playPt (cfgOf R d n m A b cs) (traj R d n m A b σ cs t).1 (drawAt R d n cs t).1) i = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · rw [Function.update_of_ne h.ne]
      exact traj_hist R d n m A b σ cs t i h
    · rw [Function.update_self]
      rfl

/-- The history before round `t` is known at `cσ d t` (`meas_comp_beta` with `traj_congr`). -/
theorem lamRaw_meas (R : Routines) (hR : PosLocal R) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (σ : Strategy d) (t : ℕ) : Measurable[cσ d t] (lamRaw R d n m A b σ t) :=
  Sched.meas_comp_beta (Y := HistQ d) d (R.K0 d n) (par d n).B t _ le_rfl (fun cs => ((traj R d n m A b σ cs t).2 : HistQ d))
    fun cs cs' h => by rw [traj_congr R hR d n m A b σ cs cs' t h]

/-- The loss parameter of the record is BL's history. -/
theorem lamR_eq (R : Routines) (hR : PosLocal R) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (σ : Strategy d) (t : ℕ) : lamR R d n m A b σ t = lamRaw R d n m A b σ t := by
  unfold lamR
  rw [ite_eq_left (lamRaw_meas R hR d n m A b σ t)]

/-! ## BL's round -/

/-- BL's mode after round `t`: `step` of the mode before it, on the draw and the reading of the round. -/
theorem modeW_succ (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) :
    modeW R d n m A b σ (t + 1) ω = step R.ap (cfgW R d n m A b ω) n (modeW R d n m A b σ t ω)
      (drawW R d n t ω).1 (drawW R d n t ω).2 (obsW R d n m A b σ t ω) := rfl

/-- BL's reading of round `t` is the floor of `2^p` times the record's loss at BL's play. -/
theorem obsW_eq (R : Routines) (hR : PosLocal R) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (σ : Strategy d) (hσ : AdmStrat (polytope A b) n σ) (t : ℕ) (ω : WΩ) :
    obsW R d n m A b σ t ω =
      ⌊(2 : ℝ) ^ (par d n).p * lossW R d n m A b σ t ω (toE (playW R d n m A b σ t ω))⌋ := by
  unfold obsW lossW lossL
  rw [lamR_eq R hR, ite_eq_left hσ, Conj1.lossAd_congr σ 0 t (y := fun i => toE (lamRaw R d n m A b σ t ω i))
    (fun i hi => congrArg toE (Function.update_of_ne hi.ne _ _))]

/-- On `Case`, BL's scale `pt'` is `ptE` of `K~` at its point. -/
theorem ptQ_cast {R : Routines} {d n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
    (hg : PgGood d (polytope A b) (po d n).R (some (posR R d n m A b cs))) (X : Fin d → ℚ) :
    ((ptQ (cfgOf R d n m A b cs) X : ℚ) : ℝ) =
      ptE (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ((par d n).eps : ℝ)
        (WithLp.toLp 2 (cV X)) := by
  have h := (rowsC R d n m A b cs hg).2.2 X
  unfold ptQ ptE
  push_cast
  rw [h]
  rfl

/-- On `Case`, BL's play in mode `run` is the play of its point `X'` at the scale `pt'`. -/
theorem playPt_run {R : Routines} {d n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
    (hg : PgGood d (polytope A b) (po d n).R (some (posR R d n m A b cs))) (st : St d) (ξ : Fin d → ℚ) :
    toE (playPt (cfgOf R d n m A b cs) (.run st) ξ) = pgMu (posR R d n m A b cs) + pgOp (posR R d n m A b cs)
      ((ptE (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ((par d n).eps : ℝ)
          (WithLp.toLp 2 (cV (XQ (cfgOf R d n m A b cs) st ξ))))⁻¹ •
        WithLp.toLp 2 (cV (XQ (cfgOf R d n m A b cs) st ξ))) := by
  rw [← ptQ_cast hg, pgOp_apply]
  ext i
  simp [playPt, toE, posR, pgMu, pgMat, pgPack, cM, Matrix.mulVec, dotProduct, cV, cfgOf, mkCfg]

/-! ## The parameters and the epoch start -/

/-- The enclosure lemma on `ε`: `0 < ε ≤ ε' ≤ 1/2` and `ε' - ε ≤ w_ε`. -/
theorem eps_facts {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) (hbud : Bud.BudOK d n) :
    0 < (po d n).eps ∧ (po d n).eps ≤ ((par d n).eps : ℝ) ∧ ((par d n).eps : ℝ) ≤ 1 / 2 ∧
      ((par d n).eps : ℝ) - (po d n).eps ≤ Bud.we d n := by
  have H := rowHyp_of d n (deltaBL d n) hd hn (deltaBL_pos hd hn) (deltaBL_lt_one hd hn) (hc.trans (by norm_num))
  have h0 : 0 < (po d n).eps := eps_pos_of_rows H
  have h1 := hbud.enc.eps_le
  have h2 := hbud.enc.eps_rel
  have htp0 : 0 ≤ Bud.tp d n := by unfold Bud.tp; positivity
  have htp1 : Bud.tp d n ≤ 1 := by
    unfold Bud.tp; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hc' : (po d n).eps ≤ 1 / 4 := hc
  unfold Bud.eps at h1 h2
  unfold Bud.we Bud.eps
  refine ⟨h0, h1, ?_, ?_⟩ <;> nlinarith

/-- `Track` at the epoch start (the enclosure lemma: `A_0`, `B_0`). -/
theorem track_init {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) (hbud : Bud.BudOK d n) :
    Track d n (init (par d n) d) (df2Init (po d n) d) 0 := by
  have H := rowHyp_of d n (deltaBL d n) hd hn (deltaBL_pos hd hn) (deltaBL_lt_one hd hn) (hc.trans (by norm_num))
  have hLe : 0 < (po d n).Le := by have := H.L504; unfold po; linarith
  have hs : 0 < (po d n).sig2 := by unfold po; rw [H.sig2]; apply div_pos one_pos; unfold po at hLe; linarith
  set s := (po d n).sig2 with hs_def
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq2 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have htp0 : 0 ≤ Bud.tp d n := by unfold Bud.tp; positivity
  have hha : Bud.hTr d n 0 = Bud.ha d n := by unfold Bud.hTr; simp
  have hha' : Bud.ha d n = Bud.tp d n * Real.sqrt (8 * Bud.Le d n) + Bud.tp d n + Bud.tp d n / 16 := by
    unfold Bud.ha; ring
  have hcM : ∀ c : ℚ, cM (c • (1 : Matrix (Fin d) (Fin d) ℚ)) = (c : ℝ) • 1 := by
    intro c; ext i j; simp only [cM, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]; split_ifs <;> simp
  have hop : ∀ c : ℝ, opN (c • (1 : Matrix (Fin d) (Fin d) ℝ)) ≤ |c| := EngL.opN_smul_one d
  have hone : ∀ c : ℝ, (1 : Matrix (Fin d) (Fin d) ℝ) + (c - 1) • 1 = c • 1 := by
    intro c; rw [sub_smul, one_smul]; abel
  have hcV0 : cV (0 : Fin d → ℚ) = 0 := by funext i; simp [cV]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; simp [cV, init, df2Init]
  · show s • (1 : Matrix (Fin d) (Fin d) ℝ) = (Real.sqrt s • 1) * (Real.sqrt s • 1)ᵀ
    rw [Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul_comm, one_mul, hsq2]
  · show s⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) * s • 1 = 1
    rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hs.ne', one_smul]
  · refine ⟨(((par d n).A0 : ℝ) / Real.sqrt s - 1) • 1, ?_, ?_⟩
    · show cM ((par d n).A0 • 1) = _ * (Real.sqrt s • 1)
      rw [hcM, hone, smul_mul_smul_comm, one_mul, div_mul_cancel₀ _ hsq.ne']
    · refine (hop _).trans ?_
      rw [hha, hha']
      have := hbud.enc.A0
      linarith
  · refine ⟨(((par d n).B0 : ℝ) * Real.sqrt s - 1) • 1, ?_, ?_⟩
    · show cM ((par d n).B0 • 1) = _ * (s⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) * (Real.sqrt s • 1))
      rw [hcM, hone, smul_mul_smul_comm, one_mul, smul_mul_smul_comm, one_mul]
      congr 1
      field_simp
      rw [Real.sq_sqrt hs.le]
    · refine (hop _).trans ?_
      rw [hha, hha']
      have := hbud.enc.B0
      have h8 : 0 ≤ Bud.tp d n * Real.sqrt (8 * Bud.Le d n) := by positivity
      linarith
  · simp [oNorm, hcV0, init, df2Init]
  · simp [init, df2Init]
  · simp [oNorm, hcV0, init, df2Init]
  · simp [init, df2Init]

/-! ## The round of the record in the coordinates of `K~` -/

/-- The loss of round `t` in the coordinates of `K~` (`f_t(S' y)`, the record's loss at the position). -/
noncomputable def FW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) : E d → ℝ :=
  fun y => lossW R d n m A b σ t ω (pgMu (posR R d n m A b (betaR R d n ω.1)) +
    pgOp (posR R d n m A b (betaR R d n ω.1)) y)

/-- BL's point `X' = μ' + (1 - λ') A' ξ'` of round `t` from the state `st`. -/
noncomputable def X1W (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (t : ℕ) (ω : WΩ)
    (st : St d) : E d :=
  WithLp.toLp 2 (cV (XQ (cfgW R d n m A b ω) st (drawW R d n t ω).1))

/-- P°'s point `X° = μ° + (1 - λ) A° ξ` of round `t` from the state `so`. -/
noncomputable def X0W (d n : ℕ) (t : ℕ) (ω : WΩ) (so : Df2St d) : E d :=
  WithLp.toLp 2 (refX (po d n) so (ξc d t ω))

section Eng

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {σ : Strategy d}

/-- On `Case`, BL's play of round `t` in mode `run st`. -/
theorem playW_run {ω : WΩ} (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) {t : ℕ} {st : St d}
    (hW : modeW R d n m A b σ t ω = .run st) :
    toE (playW R d n m A b σ t ω) = pgMu (posR R d n m A b (betaR R d n ω.1)) +
      pgOp (posR R d n m A b (betaR R d n ω.1))
        ((ptE (kW R d n m A b ω) ((par d n).eps : ℝ) (X1W R d n m A b t ω st))⁻¹ • X1W R d n m A b t ω st) := by
  show toE (playPt (cfgOf R d n m A b (betaR R d n ω.1)) (modeW R d n m A b σ t ω) (drawW R d n t ω).1) = _
  rw [hW]
  exact playPt_run hq st _

/-- On `Case`, P°'s play of round `t` from the mode `run so`, in the interior of `K`. -/
theorem refPlayW_run (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) {ω : WΩ}
    (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) {t : ℕ} {so : Df2St d}
    (hmo : (blRun R d n m A b σ).mode (deltaBL d n) t ω = .run so) :
    (blRun R d n m A b σ).refPlay (deltaBL d n) t ω = pgMu (posR R d n m A b (betaR R d n ω.1)) +
      pgOp (posR R d n m A b (betaR R d n ω.1))
        ((ptE (kW R d n m A b ω) (po d n).eps (X0W d n t ω so))⁻¹ • X0W d n t ω so) ∧
    (blRun R d n m A b σ).refPlay (deltaBL d n) t ω ∈ interior (polytope A b) := by
  have H := rowHyp_of d n (deltaBL d n) hd hn (deltaBL_pos hd hn) (deltaBL_lt_one hd hn) (hc.trans (by norm_num))
  have heps0 := eps_pos_of_rows H
  have heps1 : (df2oPar d n (deltaBL d n)).eps < 1 := by have : (po d n).eps ≤ 1 / 4 := hc; unfold po at this; linarith
  exact Run.refPlay_run _ (Conj1Poly.convex_polytope A b) hq heps0 heps1 hmo

/-- On `Case`, the record's shift of a round `t < n` of the noiseless world at which both learners are in mode `run`:
`r = pt'/pt°`, `m = 2 (ext'(X') - ext(X°))/pt°`. -/
theorem shR_run (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) {ω : WΩ}
    (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) {t : ℕ} (ht : t < n) (hz : ω.2 t = 0) {so : Df2St d}
    {st : St d} (hmo : (blRun R d n m A b σ).mode (deltaBL d n) t ω = .run so)
    (hW : modeW R d n m A b σ t ω = .run st) :
    (blRun R d n m A b σ).shR (deltaBL d n) t ω =
      (2 * (extE (kW R d n m A b ω) ((par d n).eps : ℝ) (FW R d n m A b σ t ω) (X1W R d n m A b t ω st) -
          extE (kW R d n m A b ω) (po d n).eps (FW R d n m A b σ t ω) (X0W d n t ω so)) /
          ptE (kW R d n m A b ω) (po d n).eps (X0W d n t ω so),
        ptE (kW R d n m A b ω) ((par d n).eps : ℝ) (X1W R d n m A b t ω st) /
          ptE (kW R d n m A b ω) (po d n).eps (X0W d n t ω so)) := by
  obtain ⟨hrp, hint⟩ := refPlayW_run hd hn hc hq hmo
  rw [hrp] at hint
  have hx' := playW_run hq hW
  have hlr : lossRW R d n m A b σ t ω (pgMu (posR R d n m A b (betaR R d n ω.1)) +
      pgOp (posR R d n m A b (betaR R d n ω.1))
        ((ptE (kW R d n m A b ω) (po d n).eps (X0W d n t ω so))⁻¹ • X0W d n t ω so)) =
      FW R d n m A b σ t ω ((ptE (kW R d n m A b ω) (po d n).eps (X0W d n t ω so))⁻¹ • X0W d n t ω so) := by
    unfold lossRW; rw [ite_eq_left ht]; exact fL_interior hint
  have hpt' : ((ptQ (cfgW R d n m A b ω) (XQ (cfgW R d n m A b ω) st (drawW R d n t ω).1) : ℚ) : ℝ) =
      ptE (kW R d n m A b ω) ((par d n).eps : ℝ) (X1W R d n m A b t ω st) := ptQ_cast hq _
  have hpo : refPt (po d n) (kW R d n m A b ω) (refX (po d n) so (ξc d t ω)) =
      ptE (kW R d n m A b ω) (po d n).eps (X0W d n t ω so) := rfl
  have hcf : ((cfgW R d n m A b ω).par.eps : ℝ) = ((par d n).eps : ℝ) := rfl
  have hX0 : WithLp.toLp 2 (refX (po d n) so (ξc d t ω)) = X0W d n t ω so := rfl
  have hF1 : lossW R d n m A b σ t ω (pgMu (posR R d n m A b (betaR R d n ω.1)) +
      pgOp (posR R d n m A b (betaR R d n ω.1))
        ((ptE (kW R d n m A b ω) ((par d n).eps : ℝ) (X1W R d n m A b t ω st))⁻¹ • X1W R d n m A b t ω st)) =
      FW R d n m A b σ t ω
        ((ptE (kW R d n m A b ω) ((par d n).eps : ℝ) (X1W R d n m A b t ω st))⁻¹ • X1W R d n m A b t ω st) := rfl
  have hp0 : 0 < ptE (kW R d n m A b ω) (po d n).eps (X0W d n t ω so) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  show shW R d n m A b σ t ω ((blRun R d n m A b σ).mode (deltaBL d n) t ω) = _
  rw [hmo]
  simp only [shW, hW]
  rw [hpt', hpo, hcf, WithLp.toLp_smul, hX0, hlr, hx', hz, hF1]
  unfold extE
  refine Prod.ext ?_ rfl
  field_simp
  ring

/-- `IND(t)`: before round `t` both learners are in mode `run` on one virtual epoch of P°
started before a round `a` at a fresh mode and continued through its rounds `< t - a`, with `Track` between BL's
state and P°'s. -/
def EngInv (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d) (ω : WΩ)
    (t : ℕ) : Prop :=
  ∃ a s : ℕ, ∃ st : St d, a + s = t ∧
    (blRun R d n m A b σ).mode (deltaBL d n) a ω = .run (df2Init (po d n) d) ∧
    (∀ u < s, ((blRun R d n m A b σ).ctx (deltaBL d n) a ω).cont ((blRun R d n m A b σ).path (deltaBL d n) a ω) u) ∧
    modeW R d n m A b σ t ω = .run st ∧
    Track d n st (((blRun R d n m A b σ).ctx (deltaBL d n) a ω).st ((blRun R d n m A b σ).path (deltaBL d n) a ω) s) s

/-- In `IND(t)` at `t = a + s < n` on `Case ∩ Ω_ref`: P°'s mode before round `t` is the epoch's state, DET holds at
the horizon `s + 1` and the stopping time there is `s` (the horizon lemma (c)). -/
theorem round_ctx (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) {ω : WΩ}
    (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) (hG : (blRun R d n m A b σ).Good (deltaBL d n) ω)
    {a s : ℕ} (ht : a + s < n)
    (hfa : (blRun R d n m A b σ).mode (deltaBL d n) a ω = .run (df2Init (po d n) d))
    (hcont : ∀ u < s, ((blRun R d n m A b σ).ctx (deltaBL d n) a ω).cont
      ((blRun R d n m A b σ).path (deltaBL d n) a ω) u) :
    (blRun R d n m A b σ).mode (deltaBL d n) (a + s) ω =
        .run (((blRun R d n m A b σ).ctx (deltaBL d n) a ω).st ((blRun R d n m A b σ).path (deltaBL d n) a ω) s) ∧
      DetHyp ((blRun R d n m A b σ).ctx (deltaBL d n) a ω) (deltaBL d n)
        ((blRun R d n m A b σ).path (deltaBL d n) a ω) (s + 1) ∧
      ((blRun R d n m A b σ).ctx (deltaBL d n) a ω).tau ((blRun R d n m A b σ).path (deltaBL d n) a ω) (s + 1) =
        s := by
  have hreg : Regime d n (deltaBL d n) :=
    ⟨hd, hn, deltaBL_pos hd hn, deltaBL_lt_one hd hn, hc.trans (by norm_num)⟩
  have hKc := Conj1Poly.isClosed_polytope A b
  have hKconv := Conj1Poly.convex_polytope A b
  have hm := Run.vmode _ hreg hKc hKconv hq hfa s ht.le
  have hH := Run.detHyp_of_good _ (fun v => apAdv_spec hd v) hreg hKc hKconv (by omega : a < n)
    (hG.1 a (by omega))
  obtain ⟨h1, h2⟩ := hor_step hH (by omega : s + 1 ≤ n - a) hcont
  exact ⟨hm.trans (mode_run_of_cont _ _ s hcont), h1, h2⟩

/-- On `Case`, the loss of round `s` of the epoch started before `a` is half the round's loss at the position. -/
theorem path_g {ω : WΩ} (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) {a s : ℕ} (h : a + s < n) :
    ((blRun R d n m A b σ).path (deltaBL d n) a ω).g s = fun y => FW R d n m A b σ (a + s) ω y / 2 := by
  funext y
  have hq' : PgGood d (polytope A b) (df2oPar d n (deltaBL d n)).R
      (some (posR R d n m A b (betaR R d n ω.1))) := hq
  show gTh n (deltaBL d n) (polytope A b)
    (fun t => (blRun R d n m A b σ).F.L t (lamAt n (blRun R d n m A b σ).F.lam a s ω)) a s
    (posR R d n m A b (betaR R d n ω.1)) y = _
  simp only [gTh, hq', ↓reduceIte, lamAt, h]
  rfl

/-- On `Case`, P°'s observation in round `s` of the epoch started before `a`. -/
theorem ctx_Y {ω : WΩ} (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) {a s : ℕ} (h : a + s < n) :
    ((blRun R d n m A b σ).ctx (deltaBL d n) a ω).Y ((blRun R d n m A b σ).path (deltaBL d n) a ω) s =
      ptE (kW R d n m A b ω) (po d n).eps (X0W d n (a + s) ω
          (((blRun R d n m A b σ).ctx (deltaBL d n) a ω).st ((blRun R d n m A b σ).path (deltaBL d n) a ω) s)) *
        (FW R d n m A b σ (a + s) ω
            ((ptE (kW R d n m A b ω) (po d n).eps (X0W d n (a + s) ω
              (((blRun R d n m A b σ).ctx (deltaBL d n) a ω).st
                ((blRun R d n m A b σ).path (deltaBL d n) a ω) s)))⁻¹ •
              X0W d n (a + s) ω (((blRun R d n m A b σ).ctx (deltaBL d n) a ω).st
                ((blRun R d n m A b σ).path (deltaBL d n) a ω) s)) / 2 +
          (ω.2 (a + s) + (blRun R d n m A b σ).zeta (a + s) ω
            ((blRun R d n m A b σ).mode (deltaBL d n) (a + s) ω)) / 2) +
      2 * (ptE (kW R d n m A b ω) (po d n).eps (X0W d n (a + s) ω
          (((blRun R d n m A b σ).ctx (deltaBL d n) a ω).st ((blRun R d n m A b σ).path (deltaBL d n) a ω) s)) -
        1) / (po d n).eps := by
  unfold Df2Ctx.Y Df2Ctx.play
  rw [path_g hq h, WithLp.toLp_smul]
  rfl

/-- On `Case`, the loss of a round `t < n` in the coordinates of `K~` is admissible on `K~`. -/
theorem admFW {ω : WΩ} (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) {t : ℕ} (ht : t < n) :
    AdmLoss (kW R d n m A b ω) (FW R d n m A b σ t ω) := by
  have hf : AdmLoss (polytope A b) (lossW R d n m A b σ t ω) := (blRun R d n m A b σ).F.adm t ht _
  have hq' : PgGood d (polytope A b) (df2oPar d n (deltaBL d n)).R
      (some (posR R d n m A b (betaR R d n ω.1))) := hq
  have hbody := body_good (Conj1Poly.isClosed_polytope A b) (Conj1Poly.convex_polytope A b) hq'
  unfold kW
  rw [kTh_good hq']
  refine ⟨⟨hbody.1, fun x hx y hy a' b' ha hb hab => ?_⟩, fun x hx => hf.2 _ hx.1⟩
  have := hf.1.2 hx.1 hy.1 ha hb hab
  simp only [smul_eq_mul] at this ⊢
  unfold FW
  rw [affine_comb _ x y a' b' hab]
  exact this

/-- P°'s observation of round `s` of the epoch is the record's `refYW` at P°'s state (P°'s routine of the round is the
advice `advQ` read at it). -/
theorem refYW_eq (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) {ω : WΩ}
    (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) {a s : ℕ} (h : a + s < n) {so : Df2St d}
    (hso : ((blRun R d n m A b σ).ctx (deltaBL d n) a ω).st ((blRun R d n m A b σ).path (deltaBL d n) a ω) s = so)
    (hmo : (blRun R d n m A b σ).mode (deltaBL d n) (a + s) ω = .run so) :
    refYW R d n m A b σ (a + s) ω so =
      ((blRun R d n m A b σ).ctx (deltaBL d n) a ω).Y ((blRun R d n m A b σ).path (deltaBL d n) a ω) s := by
  rw [ctx_Y hq h, hso, hmo]
  obtain ⟨hrp, hint⟩ := refPlayW_run hd hn hc hq hmo
  rw [hrp] at hint
  have hlr : lossRW R d n m A b σ (a + s) ω (pgMu (posR R d n m A b (betaR R d n ω.1)) +
      pgOp (posR R d n m A b (betaR R d n ω.1))
        ((ptE (kW R d n m A b ω) (po d n).eps (X0W d n (a + s) ω so))⁻¹ • X0W d n (a + s) ω so)) =
      FW R d n m A b σ (a + s) ω ((ptE (kW R d n m A b ω) (po d n).eps (X0W d n (a + s) ω so))⁻¹ •
        X0W d n (a + s) ω so) := by
    unfold lossRW; rw [ite_eq_left h]; exact fL_interior hint
  have hpo : refPt (po d n) (kW R d n m A b ω) (refX (po d n) so (ξc d (a + s) ω)) =
      ptE (kW R d n m A b ω) (po d n).eps (X0W d n (a + s) ω so) := rfl
  have hX0 : WithLp.toLp 2 (refX (po d n) so (ξc d (a + s) ω)) = X0W d n (a + s) ω so := rfl
  unfold refYW
  dsimp only
  rw [hpo, WithLp.toLp_smul, hX0, hlr]
  show _ = _ * (_ / 2 + (ω.2 (a + s) + coupMax (shW R d n m A b σ (a + s) ω (.run so)).1
    (shW R d n m A b σ (a + s) ω (.run so)).2 (zc d (a + s) ω)) / 2) + _
  ring

/-- On the noiseless world, if round `t = a + s` does not decouple, P°'s observation is BL's exact observation. -/
theorem cY_coupled (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) {ω : WΩ}
    (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) {a s : ℕ} (h : a + s < n) (hz : ω.2 (a + s) = 0)
    {so : Df2St d} {st : St d}
    (hso : ((blRun R d n m A b σ).ctx (deltaBL d n) a ω).st ((blRun R d n m A b σ).path (deltaBL d n) a ω) s = so)
    (hmo : (blRun R d n m A b σ).mode (deltaBL d n) (a + s) ω = .run so)
    (hW : modeW R d n m A b σ (a + s) ω = .run st) (hD : ¬ (blRun R d n m A b σ).D (deltaBL d n) (a + s) ω) :
    ((blRun R d n m A b σ).ctx (deltaBL d n) a ω).Y ((blRun R d n m A b σ).path (deltaBL d n) a ω) s =
      ((ptQ (cfgOf R d n m A b (betaR R d n ω.1))
          (XQ (cfgOf R d n m A b (betaR R d n ω.1)) st (drawW R d n (a + s) ω).1) : ℚ) : ℝ) *
        (lossW R d n m A b σ (a + s) ω (toE (playPt (cfgOf R d n m A b (betaR R d n ω.1)) (.run st)
          (drawW R d n (a + s) ω).1)) + zc d (a + s) ω 0 / 2) / 2 +
      2 * (((ptQ (cfgOf R d n m A b (betaR R d n ω.1))
          (XQ (cfgOf R d n m A b (betaR R d n ω.1)) st (drawW R d n (a + s) ω).1) : ℚ) : ℝ) - 1) /
        (((cfgOf R d n m A b (betaR R d n ω.1)).par.eps : ℚ) : ℝ) := by
  have hD' : (blRun R d n m A b σ).zeta (a + s) ω ((blRun R d n m A b σ).mode (deltaBL d n) (a + s) ω) =
      ((blRun R d n m A b σ).shR (deltaBL d n) (a + s) ω).1 +
        ((blRun R d n m A b σ).shR (deltaBL d n) (a + s) ω).2 * zc d (a + s) ω 0 / 2 := not_not.mp hD
  rw [ctx_Y hq h, hso, hD', shR_run hd hn hc hq h hz hmo hW, hz]
  have e1 : ((ptQ (cfgOf R d n m A b (betaR R d n ω.1))
      (XQ (cfgOf R d n m A b (betaR R d n ω.1)) st (drawW R d n (a + s) ω).1) : ℚ) : ℝ) =
      ptE (kW R d n m A b ω) ((par d n).eps : ℝ) (X1W R d n m A b (a + s) ω st) := ptQ_cast hq _
  have e2 : toE (playPt (cfgOf R d n m A b (betaR R d n ω.1)) (.run st) (drawW R d n (a + s) ω).1) =
      pgMu (posR R d n m A b (betaR R d n ω.1)) + pgOp (posR R d n m A b (betaR R d n ω.1))
        ((ptE (kW R d n m A b ω) ((par d n).eps : ℝ) (X1W R d n m A b (a + s) ω st))⁻¹ •
          X1W R d n m A b (a + s) ω st) := playPt_run hq st _
  have e3 : (((cfgOf R d n m A b (betaR R d n ω.1)).par.eps : ℚ) : ℝ) = ((par d n).eps : ℝ) := rfl
  have hF1 : lossW R d n m A b σ (a + s) ω (pgMu (posR R d n m A b (betaR R d n ω.1)) +
      pgOp (posR R d n m A b (betaR R d n ω.1))
        ((ptE (kW R d n m A b ω) ((par d n).eps : ℝ) (X1W R d n m A b (a + s) ω st))⁻¹ •
          X1W R d n m A b (a + s) ω st)) =
      FW R d n m A b σ (a + s) ω ((ptE (kW R d n m A b ω) ((par d n).eps : ℝ) (X1W R d n m A b (a + s) ω st))⁻¹ •
        X1W R d n m A b (a + s) ω st) := rfl
  rw [e1, e2, e3, hF1]
  have hp0 : 0 < ptE (kW R d n m A b ω) (po d n).eps (X0W d n (a + s) ω so) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold extE
  field_simp
  ring

/-- On `Case`, BL starts in mode `run` (P5 MODE: `ε' ≤ 1/2` and the kept `β̃_i > 0`). -/
theorem modeW_zero {ω : WΩ} (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω)
    (heps : ((par d n).eps : ℝ) ≤ 1 / 2) : modeW R d n m A b σ 0 ω = .run (init (par d n) d) := by
  have hβ := (rowsC R d n m A b (betaR R d n ω.1) hq).2.1
  have hcond : ¬ (1 / 2 < (cfgOf R d n m A b (betaR R d n ω.1)).par.eps ∨
      ∃ i, (cfgOf R d n m A b (betaR R d n ω.1)).β i ≤ 0) := by
    push Not
    refine ⟨?_, hβ⟩
    show (par d n).eps ≤ 1 / 2
    have h2 : (((par d n).eps : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by push_cast; exact heps
    exact Rat.cast_le.mp h2
  show mode0 (cfgOf R d n m A b (betaR R d n ω.1)) = _
  unfold mode0
  rw [ite_eq_right_iff.mpr (fun h => absurd h hcond)]
  rfl

/-- `IND(0)`. -/
theorem inv_zero (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) (hbud : Bud.BudOK d n) {ω : WΩ}
    (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) : EngInv R d n m A b σ ω 0 :=
  ⟨0, 0, init (par d n) d, rfl, rfl, fun u hu => absurd hu (Nat.not_lt_zero u),
    modeW_zero hq (eps_facts hd hn hc hbud).2.2.1, track_init hd hn hc hbud⟩

/-- `IND(t) → IND(t + 1)` at a round `t < n` that does not decouple, on `Case ∩ Ω_ref ∩ E_bits ∩ Z_n`: piece C
(`RoundC`) in the epoch's round `s`, then the horizon lemma at a fire (a fresh epoch before round `t + 1`). -/
theorem inv_succ (hO3 : O3SpecQ R.ap) (hR : PosLocal R) (hC : RoundC) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hc : RunCase d n) (hbud : Bud.BudOK d n) (hσ : AdmStrat (polytope A b) n σ) {ω : WΩ}
    (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) (hG : (blRun R d n m A b σ).Good (deltaBL d n) ω)
    (hbits : ω ∈ Ebits R d n ∩ Zn n) {t : ℕ} (ht : t < n) (hD : ¬ (blRun R d n m A b σ).D (deltaBL d n) t ω)
    (hI : EngInv R d n m A b σ ω t) : EngInv R d n m A b σ ω (t + 1) := by
  obtain ⟨a, s, st, rfl, hfa, hcont, hW, htr⟩ := hI
  obtain ⟨hmo, hdet, htau⟩ := round_ctx hd hn hc hq hG ht hfa hcont
  have hreg : Regime d n (deltaBL d n) :=
    ⟨hd, hn, deltaBL_pos hd hn, deltaBL_lt_one hd hn, hc.trans (by norm_num)⟩
  have hrows := rowsC R d n m A b (betaR R d n ω.1) hq
  have hadm : AdmLoss (polytope A b) (lossW R d n m A b σ (a + s) ω) :=
    (blRun R d n m A b σ).F.adm (a + s) ht _
  have hg := path_g hq ht
  have hb := hbits.1 (a + s) ht
  have hz : ω.2 (a + s) = 0 := hbits.2 (a + s) ht
  have hY := cY_coupled hd hn hc hq ht hz rfl hmo hW hD
  have hpl : playW R d n m A b σ (a + s) ω =
      playPt (cfgOf R d n m A b (betaR R d n ω.1)) (.run st) (drawW R d n (a + s) ω).1 := by
    show playPt _ (modeW R d n m A b σ (a + s) ω) _ = _
    rw [hW]
    rfl
  have hobs : obsW R d n m A b σ (a + s) ω = ⌊(2 : ℝ) ^ (cfgOf R d n m A b (betaR R d n ω.1)).par.p *
      lossW R d n m A b σ (a + s) ω (toE (playPt (cfgOf R d n m A b (betaR R d n ω.1)) (.run st)
        (drawW R d n (a + s) ω).1))⌋ := by
    rw [obsW_eq R hR d n m A b σ hσ, hpl]
    rfl
  have hap : apAdv ((blRun R d n m A b σ).adv (a + s) ω ((blRun R d n m A b σ).mode (deltaBL d n) (a + s) ω)) =
      apAdv (advQ R.ap (cfgOf R d n m A b (betaR R d n ω.1)) n st (drawW R d n (a + s) ω).1
        (drawW R d n (a + s) ω).2 ⌊(2 : ℝ) ^ (cfgOf R d n m A b (betaR R d n ω.1)).par.p *
          lossW R d n m A b σ (a + s) ω (toE (playPt (cfgOf R d n m A b (betaR R d n ω.1)) (.run st)
            (drawW R d n (a + s) ω).1))⌋
        (df2oPar d n (deltaBL d n))
        (((blRun R d n m A b σ).ctx (deltaBL d n) a ω).st ((blRun R d n m A b σ).path (deltaBL d n) a ω) s)
        (ξc d (a + s) ω)
        (((blRun R d n m A b σ).ctx (deltaBL d n) a ω).Y ((blRun R d n m A b σ).path (deltaBL d n) a ω) s)) := by
    rw [hmo]
    show apAdv (advW R d n m A b σ (a + s) ω (.run _)) = _
    simp only [advW, hW]
    rw [hobs, refYW_eq hd hn hc hq ht rfl hmo]
    rfl
  have hRC := hC R d n m A b (betaR R d n ω.1) _ ((blRun R d n m A b σ).path (deltaBL d n) a ω) s st
    (drawW R d n (a + s) ω).1 (drawW R d n (a + s) ω).2 (zc d (a + s) ω 0) (lossW R d n m A b σ (a + s) ω)
    hd hn hc hbud hO3 hq hrows.1 hrows.2.1 hrows.2.2 (by omega) hdet htau htr hadm
    (fun y => by rw [hg]; rfl) hb.1 hb.2 hY hap
  have hstep : modeW R d n m A b σ (a + s + 1) ω = step R.ap (cfgOf R d n m A b (betaR R d n ω.1)) n (.run st)
      (drawW R d n (a + s) ω).1 (drawW R d n (a + s) ω).2 ⌊(2 : ℝ) ^ (cfgOf R d n m A b (betaR R d n ω.1)).par.p *
        lossW R d n m A b σ (a + s) ω (toE (playPt (cfgOf R d n m A b (betaR R d n ω.1)) (.run st)
          (drawW R d n (a + s) ω).1))⌋ := by
    rw [modeW_succ, hW, hobs]
    rfl
  rcases hRC with ⟨hf1, hf2⟩ | ⟨st', hs1, hs2, hs3⟩
  · have hm1 : (blRun R d n m A b σ).mode (deltaBL d n) (a + s + 1) ω = .run (df2Init (po d n) d) := by
      have h1 := Run.vmode _ hreg (Conj1Poly.isClosed_polytope A b) (Conj1Poly.convex_polytope A b) hq hfa (s + 1)
        (by omega)
      rw [← add_assoc] at h1
      rw [h1]
      exact hf2
    refine ⟨a + s + 1, 0, init (par d n) d, by omega, hm1, fun u hu => absurd hu (Nat.not_lt_zero u), ?_,
      track_init hd hn hc hbud⟩
    rw [hstep]
    exact hf1
  · refine ⟨a, s + 1, st', by omega, hfa, ?_, ?_, hs3⟩
    · intro u hu
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
      · exact hcont u hu
      · exact hs2
    · rw [hstep]
      exact hs1

/-- `IND(t)` at every round `t ≤ n` before which no round decoupled. -/
theorem ind (hO3 : O3SpecQ R.ap) (hR : PosLocal R) (hC : RoundC) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hc : RunCase d n) (hbud : Bud.BudOK d n) (hσ : AdmStrat (polytope A b) n σ) {ω : WΩ}
    (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) (hG : (blRun R d n m A b σ).Good (deltaBL d n) ω)
    (hbits : ω ∈ Ebits R d n ∩ Zn n) :
    ∀ t ≤ n, (∀ u < t, ¬ (blRun R d n m A b σ).D (deltaBL d n) u ω) → EngInv R d n m A b σ ω t := by
  intro t
  induction t with
  | zero => intro _ _; exact inv_zero hd hn hc hbud hq
  | succ t ih =>
    intro ht hD
    exact inv_succ hO3 hR hC hd hn hc hbud hσ hq hG hbits (by omega) (hD t (by omega))
      (ih (by omega) fun u hu => hD u (by omega))

/-- The shift and the regret of a round `t < n` in `IND(t)` on `Case ∩ Ω_ref ∩ E_bits ∩ Z_n`: piece C (`PlayC`),
Lemma MPAR and the coupling lemma with `κ1 = 0` for the shift, the play gap of E17 for the regret. -/
theorem round_bound (hP : PlayC) (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) (hbud : Bud.BudOK d n) {ω : WΩ}
    (hq : (blRun R d n m A b σ).Case (deltaBL d n) ω) (hG : (blRun R d n m A b σ).Good (deltaBL d n) ω)
    (hbits : ω ∈ Ebits R d n ∩ Zn n) {t : ℕ} (ht : t < n) (hI : EngInv R d n m A b σ ω t) :
    (0 < ((blRun R d n m A b σ).shR (deltaBL d n) t ω).2 ∧
      tvB ((blRun R d n m A b σ).shR (deltaBL d n) t ω).1 ((blRun R d n m A b σ).shR (deltaBL d n) t ω).2 ≤
        Bud.kap0 d n) ∧
    lossW R d n m A b σ t ω (toE (playW R d n m A b σ t ω)) ≤
      lossW R d n m A b σ t ω ((blRun R d n m A b σ).refPlay (deltaBL d n) t ω) +
        ((1 + 2 * Bud.R d n) * Bud.Xb d n + 4 * Bud.R d n * Bud.pib d n * Bud.we d n) / Bud.eps d n := by
  obtain ⟨a, s, st, rfl, hfa, hcont, hW, htr⟩ := hI
  obtain ⟨hmo, hdet, htau⟩ := round_ctx hd hn hc hq hG ht hfa hcont
  set so := ((blRun R d n m A b σ).ctx (deltaBL d n) a ω).st ((blRun R d n m A b σ).path (deltaBL d n) a ω) s
    with hso
  set Kt := kW R d n m A b ω with hKt
  set F := FW R d n m A b σ (a + s) ω with hF
  set X1 := X1W R d n m A b (a + s) ω st with hX1
  set X0 := X0W d n (a + s) ω so with hX0
  have H := rowHyp_of d n (deltaBL d n) hd hn (deltaBL_pos hd hn) (deltaBL_lt_one hd hn) (hc.trans (by norm_num))
  have hR1 : 1 ≤ (df2oPar d n (deltaBL d n)).R := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n (deltaBL d n)).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  have hLe0 : 0 ≤ (po d n).Le := by have := H.L504; unfold po; linarith
  obtain ⟨he0, hee, he', hwe⟩ := eps_facts hd hn hc hbud
  have hbody : Df2Body d (df2oPar d n (deltaBL d n)).R Kt :=
    body_kTh (Conj1Poly.isClosed_polytope A b) (Conj1Poly.convex_polytope A b) hR1 hmw _
  obtain ⟨hconv, hclosed, h1, hRb, -⟩ := id hbody
  have hFa : AdmLoss Kt F := admFW hq ht
  have heps1 : (po d n).eps < 1 := by linarith
  have hlip : ∀ x y : E d, (1 - (po d n).eps)⁻¹ • x ∈ Kt → (1 - (po d n).eps)⁻¹ • y ∈ Kt →
      F y - F x ≤ ‖y - x‖ / (po d n).eps :=
    fun x y hx hy => PropG.convex_lip_eps Kt hconv h1 F hFa.1 hFa.2 _ he0 heps1 x y hx hy
  have hconvF2 : ConvexOn ℝ Kt (fun y => F y / 2) := by
    refine (hFa.1.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).congr fun y _ => ?_
    simp only [smul_eq_mul]; ring
  have hF2 : AdmLoss Kt (fun y => F y / 2) :=
    ⟨hconvF2, fun x hx => ⟨by linarith [(hFa.2 x hx).1], by linarith [(hFa.2 x hx).2]⟩⟩
  have hSI := (SIF.df2SIFacts_holds d n (deltaBL d n) Kt (fun y => F y / 2) hd hn (deltaBL_pos hd hn)
    (deltaBL_lt_one hd hn) (hc.trans (by norm_num)) hbody hF2).1.2.2.1
  have hext : ∀ x y : E d, |extE Kt (po d n).eps F x - extE Kt (po d n).eps F y| ≤
      8 / (po d n).eps * ‖x - y‖ := by
    intro x y
    have e : ∀ z, df2Ext (df2oPar d n (deltaBL d n)) Kt (fun y => F y / 2) z = extE Kt (po d n).eps F z := by
      intro z; unfold df2Ext df2Pip extE ptE po; ring
    have := hSI x y
    rwa [e, e] at this
  have hb := hbits.1 (a + s) ht
  have hz : ω.2 (a + s) = 0 := hbits.2 (a + s) ht
  have hXP := hP R d n m A b (betaR R d n ω.1) _ ((blRun R d n m A b σ).path (deltaBL d n) a ω) s st
    (drawW R d n (a + s) ω).1 hd hn hc hbud hq (by omega) hdet htau htr hb.1
  have hX : ‖X1 - X0‖ ≤ Bud.Xb d n := by
    rw [hX1, hX0, X1W, X0W, ← WithLp.toLp_sub, ← LeanAp.oNorm_eq]; exact hXP
  have hg0 : gauge Kt X0 ≤ Real.sqrt (po d n).Le := (hdet.evG s (by rw [htau])).2.1
  have hpib0 : 0 ≤ Bud.pib d n := by unfold Bud.pib; positivity
  have hR0 : 0 ≤ Bud.R d n := by show 0 ≤ (po d n).R; unfold po; linarith
  have hsh : |ptE Kt ((par d n).eps : ℝ) X1 / ptE Kt (po d n).eps X0 - 1| +
      |2 * (extE Kt ((par d n).eps : ℝ) F X1 - extE Kt (po d n).eps F X0) / ptE Kt (po d n).eps X0| ≤
      (2 + 16 / Bud.eps d n) * Bud.Xb d n + (4 * Bud.pib d n * (((par d n).eps : ℝ) - Bud.eps d n) +
        2 * Bud.pib d n * (Bud.R d n + 9) * (((par d n).eps : ℝ) - Bud.eps d n) / Bud.eps d n ^ 2) :=
    EngL.ext_lip_shift Kt hconv hclosed h1 _ hRb F hFa.2 _ _ he0 hee he' hlip hext (po d n).Le (Bud.Xb d n) hLe0
      hbud.Xb_le X1 X0 hg0 hX
  have hmp : 4 * Bud.pib d n * (((par d n).eps : ℝ) - Bud.eps d n) +
      2 * Bud.pib d n * (Bud.R d n + 9) * (((par d n).eps : ℝ) - Bud.eps d n) / Bud.eps d n ^ 2 ≤
      Bud.tp d n / 4 * Bud.pib d n * (Bud.R d n + 10) / Bud.eps d n :=
    EngL.mpar_le _ _ _ _ _ hpib0 hR0 he0 (by show (po d n).eps ≤ 1 / 2; linarith) (sub_nonneg.2 hee) hwe
  have hk3 : 3 / 4 * Bud.kap0 d n = (2 + 16 / Bud.eps d n) * Bud.Xb d n +
      Bud.tp d n / 4 * Bud.pib d n * (Bud.R d n + 10) / Bud.eps d n := by
    unfold Bud.kap0 Bud.mpar; ring
  have hk : Bud.kap0 d n ≤ 1 / 4 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hk0 := hbud.kap0_nonneg
    have hdb : 0 ≤ Bud.dbits d n := by unfold Bud.dbits Bud.tp; positivity
    have h1 : Bud.kap0 d n ≤ (n : ℝ) * Bud.kap0 d n := le_mul_of_one_le_left hk0 hn1
    have h2 : (n : ℝ) * Bud.kap0 d n ≤ n * (n * Bud.kap0 d n) := le_mul_of_one_le_left (by positivity) hn1
    have h3 : (n : ℝ) * (n * Bud.kap0 d n) ≤ n * (Bud.dbits d n + n * Bud.kap0 d n) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [hbud.budget]
  rw [shR_run hd hn hc hq ht hz hmo hW]
  refine ⟨EngL.tv_le _ _ _ hk (by linarith), ?_⟩
  have hgap : |F ((ptE Kt ((par d n).eps : ℝ) X1)⁻¹ • X1) - F ((ptE Kt (po d n).eps X0)⁻¹ • X0)| ≤
      ((1 + 2 * Bud.R d n) * Bud.Xb d n + 4 * Bud.R d n * Bud.pib d n * (((par d n).eps : ℝ) - Bud.eps d n)) /
        Bud.eps d n :=
    EngL.play_gap Kt hconv hclosed h1 _ hRb F _ _ he0 hee he' hlip (po d n).Le (Bud.Xb d n) hLe0 hbud.Xb_le X1 X0
      hg0 hX
  have hp1 : lossW R d n m A b σ (a + s) ω (toE (playW R d n m A b σ (a + s) ω)) =
      F ((ptE Kt ((par d n).eps : ℝ) X1)⁻¹ • X1) := by
    rw [playW_run hq hW]
    rfl
  have hp0 : lossW R d n m A b σ (a + s) ω ((blRun R d n m A b σ).refPlay (deltaBL d n) (a + s) ω) =
      F ((ptE Kt (po d n).eps X0)⁻¹ • X0) := by
    rw [(refPlayW_run hd hn hc hq hmo).1]
    rfl
  rw [hp1, hp0]
  have hw4 : 4 * Bud.R d n * Bud.pib d n * (((par d n).eps : ℝ) - Bud.eps d n) ≤
      4 * Bud.R d n * Bud.pib d n * Bud.we d n :=
    mul_le_mul_of_nonneg_left hwe (mul_nonneg (mul_nonneg (by norm_num) hR0) hpib0)
  have hmono : ((1 + 2 * Bud.R d n) * Bud.Xb d n + 4 * Bud.R d n * Bud.pib d n *
      (((par d n).eps : ℝ) - Bud.eps d n)) / Bud.eps d n ≤
      ((1 + 2 * Bud.R d n) * Bud.Xb d n + 4 * Bud.R d n * Bud.pib d n * Bud.we d n) / Bud.eps d n :=
    div_le_div_of_nonneg_right (by linarith) he0.le
  linarith [le_abs_self (F ((ptE Kt ((par d n).eps : ℝ) X1)⁻¹ • X1) - F ((ptE Kt (po d n).eps X0)⁻¹ • X0))]

end Eng

/-- Step 1 of SHADOW for the record: `EngineHyp` with `κ0 = Bud.kap0`, `κ1 = 0`. -/
theorem engine_of {R : Routines} (hO3 : O3SpecQ R.ap) (hR : PosLocal R) (hA : BudA) (hP : PlayC) (hC : RoundC)
    {d n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hI : InputOK d n m M A b) (hc : RunCase d n)
    {σ : Strategy d} (hσ : AdmStrat (polytope A b) n σ) :
    EngineHyp (blRun R d n m A b σ) (deltaBL d n) (Bud.kap0 d n) 0 := by
  have hbud := hA d n hI.hd hI.hn hc
  refine ⟨fun ω hq hG hbits t ht hD => ?_, fun ω hq hG hbits hD => ?_⟩
  · have hI' := ind hO3 hR hC hI.hd hI.hn hc hbud hσ hq hG hbits t ht.le hD
    obtain ⟨⟨h1, h2⟩, -⟩ := round_bound hP hI.hd hI.hn hc hbud hq hG hbits ht hI'
    exact ⟨h1, by rw [zero_mul, add_zero]; exact h2⟩
  · have hround : ∀ t ∈ Finset.range n, (blRun R d n m A b σ).loss ω t ((blRun R d n m A b σ).play t ω) ≤
        (blRun R d n m A b σ).loss ω t ((blRun R d n m A b σ).refPlay (deltaBL d n) t ω) +
          ((1 + 2 * Bud.R d n) * Bud.Xb d n + 4 * Bud.R d n * Bud.pib d n * Bud.we d n) / Bud.eps d n := by
      intro t ht
      rw [Finset.mem_range] at ht
      exact (round_bound hP hI.hd hI.hn hc hbud hq hG hbits ht
        (ind hO3 hR hC hI.hd hI.hn hc hbud hσ hq hG hbits t ht.le fun u hu => hD u (hu.trans ht))).2
    have hreg : (n : ℝ) * (((1 + 2 * Bud.R d n) * Bud.Xb d n + 4 * Bud.R d n * Bud.pib d n * Bud.we d n) /
        Bud.eps d n) = Bud.reg d n := by
      unfold Bud.reg; ring
    calc ∑ t ∈ Finset.range n, (blRun R d n m A b σ).loss ω t ((blRun R d n m A b σ).play t ω)
        ≤ ∑ t ∈ Finset.range n, ((blRun R d n m A b σ).loss ω t ((blRun R d n m A b σ).refPlay (deltaBL d n) t ω) +
          ((1 + 2 * Bud.R d n) * Bud.Xb d n + 4 * Bud.R d n * Bud.pib d n * Bud.we d n) / Bud.eps d n) :=
          Finset.sum_le_sum hround
      _ = ∑ t ∈ Finset.range n, (blRun R d n m A b σ).loss ω t ((blRun R d n m A b σ).refPlay (deltaBL d n) t ω) +
          Bud.reg d n := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hreg]
      _ ≤ _ := by linarith [hbud.reg_le]

end AdversarialBco.Bit.BLP
