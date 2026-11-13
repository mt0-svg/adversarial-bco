/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowDet

@[expose] public section

/-!
# Proposition W-DET: the regret of P° on `Case ∩ Ω_ref`

* `Run.rr`: the run record of P° on the world `ω` (BL's position, the checked advice routine of each round, the
  draws, the noise and the coupled dither);
* `Run.mode_rr`, `Run.refPlay_rr`, `Run.mean_rr`: on `Case`, P°'s run is the run of the record up to the horizon
  (the gauges of `kTh` and of the positioned body agree, `fL` and the loss agree on the interior of `K`, where every
  play lies);
* `Run.epochOK_of_good`: on `Case`, the five events of the virtual epoch started at `a` give its `EpochOK` (DET with a
  routine per round, `df2DetF_holds`), on the path of the record;
* `Run.wdet` (Proposition W-DET): on `Case ∩ Ω_ref`, P°'s regret is at most `B_n`, given `ApSpec` of the checked
  advice routine for every advice.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2
open AdversarialBco.Poly.Conj1 (fL lamAt)

variable {d : ℕ}

theorem RunRec.mode_succ (ρ : RunRec d) (t : ℕ) : ρ.mode (t + 1) = (ρ.rnd t (ρ.mode t)).2 := by
  show (ρ.rnd (0 + t) (ρ.frm 0 _ t)).2 = _
  rw [Nat.zero_add]
  rfl

namespace Run

variable {n : ℕ} {K : Set (E d)} (B : Run d n K) (δ : ℝ)

/-- The run record of P° on the world `ω`. -/
noncomputable def rr (ω : WΩ) : RunRec d :=
  ⟨n, δ, K, B.loss ω, B.pos ω, fun t => apAdv (B.adv t ω (B.mode δ t ω)), fun t => ξc d t ω, fun t => ω.2 t,
    fun t => B.zeta t ω (B.mode δ t ω)⟩

variable {B δ}

section Case

variable (hKconv : Convex ℝ K) {ω : WΩ} (hq : B.Case δ ω) (heps0 : 0 < (df2oPar d n δ).eps)
  (heps1 : (df2oPar d n δ).eps < 1)
include hKconv hq heps0 heps1

theorem round_rr {t : ℕ} (ht : t < n) (m : Df2Mode d) :
    cRoundA n δ K (B.pos ω) (apAdv (B.adv t ω (B.mode δ t ω))) (B.lossR t ω) (ω.2 t) (ξc d t ω)
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
    (hKconv : Convex ℝ K) {ω : WΩ} (hq : B.Case δ ω) {a : ℕ} (ha : a < n)
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
    (fun s => hAP _) (fun s hs => adm_gTh (f := fun t => B.F.L t (lamAt n B.F.lam a s ω)) (a := a) (s := s) hKconv hKc
      hR hmw (B.F.adm (a + s) (by omega) _) _)
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
  show gTh n δ K (fun t => B.F.L t (lamAt n B.F.lam a s ω)) a s (B.pos ω) y =
    B.F.L (a + s) (B.F.lam (a + s) ω) (pgMu (B.pos ω) + pgOp (B.pos ω) y) / 2
  simp only [gTh, hq', ↓reduceIte, lamAt, has]

/-- Proposition W-DET: on `Case ∩ Ω_ref`, P°'s regret over the `n` rounds is at most `B_n`. -/
theorem wdet (hAP : ∀ v : Adv d, ApSpec (apAdv v)) (hreg : Regime d n δ) (hKc : IsClosed K)
    (hKconv : Convex ℝ K) {ω : WΩ} (hq : B.Case δ ω) (hg : B.Good δ ω) :
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

end Run

end AdversarialBco.Bit.Cpl
