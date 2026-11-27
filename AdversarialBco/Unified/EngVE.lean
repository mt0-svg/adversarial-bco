/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.WorldShadowRef
public import AdversarialBco.Bit.BLEngine

@[expose] public section

/-!
# The virtual epochs of P° on an abstract coupled world

Bit/BLEngine.lean's `Run.vmode`, `Run.detHyp_of_good`, `Run.refPlay_run` on `RunW` (Unified/WorldCore.lean), over
the record `RunW.rr` of Unified/WorldShadowRef.lean, verbatim with the world `Ω` in place of `WΩ`:

* `RunW.vmode`: on `Case`, from a fresh mode before round `a`, P°'s mode before round `a + s ≤ n` is the mode of the
  virtual epoch started before `a`;
* `RunW.detHyp_of_good`: the five events of the virtual epoch started at `a < n` at the horizon `n - a` give DET's
  hypotheses there;
* `RunW.refPlay_run`: on `Case`, P°'s play from the mode `.run so` is the play of its point `X°` at the scale `pt°`,
  in the interior of `K`.
-/

open MeasureTheory
open scoped Matrix

namespace AdversarialBco.Unified.World

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Poly.Conj1 (fL)

variable {d : ℕ}

namespace RunW

variable {Ω : Type} [MeasurableSpace Ω] {W : CWorld d Ω}


variable {n : ℕ} {K : Set (E d)} (B : RunW d n K W) {δ : ℝ}

/-- On `Case`, from a fresh mode before round `a`, P°'s mode before round `a + s ≤ n` is the mode of the virtual
epoch started before `a`. -/
theorem vmode (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K) {ω : Ω} (hq : B.Case δ ω) {a : ℕ}
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
    unfold RunW.ctx RunRec.ctxAt
    rw [kTh_good hq]
    rfl
  refine hfr.trans ?_
  rw [hc]
  refine ctx_mode_congr (ρ.ctxAt a) (ρ.pathAt a) (B.path δ a ω) (n - a) (fun s' hs' => ⟨?_, rfl, rfl⟩) s
    (by omega)
  funext y
  have has : a + s' < n := by omega
  symm
  show gTh n δ K (fun t => B.F.L t (lamAtW n B.F.lam a s' ω)) a s' (B.pos ω) y =
    B.F.L (a + s') (B.F.lam (a + s') ω) (pgMu (B.pos ω) + pgOp (B.pos ω) y) / 2
  have hq'' : PgGood d K (df2oPar d n δ).R (some (B.pos ω)) := hq
  simp only [gTh, hq'', ↓reduceIte, lamAtW, has]

/-- DET's hypotheses for the virtual epoch started at `a < n`, at the horizon `n - a`, from its five events. -/
theorem detHyp_of_good (hAP : ∀ v : Adv d, ApSpec (apAdv v)) (hreg : Regime d n δ) (hKc : IsClosed K)
    (hKconv : Convex ℝ K) {ω : Ω} {a : ℕ} (ha : a < n)
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
    (fun s => hAP _) (fun s hs => adm_gTh (f := fun t => B.F.L t (lamAtW n B.F.lam a s ω)) (a := a) (s := s)
      hKconv hKc hR hmw (B.F.adm (a + s) (by omega) _) _)) evG evY evLQ evSDF evDQ

/-- On `Case`, P°'s play from the mode `.run so` is the play of its point `X°` at the scale `pt°`, in the interior
of `K`. -/
theorem refPlay_run (hKconv : Convex ℝ K) {ω : Ω} (hq : B.Case δ ω) (heps0 : 0 < (df2oPar d n δ).eps)
    (heps1 : (df2oPar d n δ).eps < 1) {t : ℕ} {so : Df2St d} (hmo : B.mode δ t ω = .run so) :
    B.refPlay δ t ω = pgMu (B.pos ω) + pgOp (B.pos ω)
      ((Bit.BLP.EngL.ptE (kTh n δ K (B.pos ω)) (df2oPar d n δ).eps
          (WithLp.toLp 2 (so.mu + (1 - (df2oPar d n δ).lam) • (so.A *ᵥ W.xi t ω))))⁻¹ •
        WithLp.toLp 2 (so.mu + (1 - (df2oPar d n δ).lam) • (so.A *ᵥ W.xi t ω))) ∧
    B.refPlay δ t ω ∈ interior K := by
  set X : Fin d → ℝ := so.mu + (1 - (df2oPar d n δ).lam) • (so.A *ᵥ W.xi t ω) with hX
  have hint := play_interior hKconv hq heps0 heps1 (WithLp.toLp 2 X)
  have hpt : Bit.BLP.EngL.ptE (kTh n δ K (B.pos ω)) (df2oPar d n δ).eps (WithLp.toLp 2 X) =
      df2Pip (df2oPar d n δ) (df2Kp K (B.pos ω) (df2oPar d n δ).R) (WithLp.toLp 2 X) := by
    rw [kTh_good hq]; rfl
  have hval : B.refPlay δ t ω = pgMu (B.pos ω) + pgOp (B.pos ω)
      ((df2Pip (df2oPar d n δ) (df2Kp K (B.pos ω) (df2oPar d n δ).R) (WithLp.toLp 2 X))⁻¹ • WithLp.toLp 2 X) := by
    unfold RunW.refPlay cRoundA
    rw [hmo]
    simp only [df2RoundGa]
    rw [kTh_good hq]
    split_ifs with h
    · rw [WithLp.toLp_smul]; rfl
    · exact absurd (by rw [WithLp.toLp_smul]; exact interior_subset hint) h
  rw [hpt]
  exact ⟨hval, hval ▸ hint⟩

/-- On `Case`, the loss of round `s` of the epoch started before `a` is half the round's loss at the position. -/
theorem path_g {ω : Ω} (hq : B.Case δ ω) {a s : ℕ} (h : a + s < n) :
    (B.path δ a ω).g s = fun y => B.loss ω (a + s) (pgMu (B.pos ω) + pgOp (B.pos ω) y) / 2 := by
  funext y
  have hq' : PgGood d K (df2oPar d n δ).R (some (B.pos ω)) := hq
  show gTh n δ K (fun t => B.F.L t (lamAtW n B.F.lam a s ω)) a s (B.pos ω) y = _
  simp only [gTh, hq', ↓reduceIte, lamAtW, h]
  rfl

/-- On `Case`, P°'s observation in round `s` of the epoch started before `a`: `pt° (f(x°)/2 + (ε + ζ*)/2) +
2 (pt° - 1)/ε` at P°'s point `X° = μ° + (1 - λ) A° ξ` of the epoch's state. -/
theorem ctx_Y {ω : Ω} (hq : B.Case δ ω) {a s : ℕ} (h : a + s < n) {so : Df2St d}
    (hso : (B.ctx δ a ω).st (B.path δ a ω) s = so) :
    (B.ctx δ a ω).Y (B.path δ a ω) s =
      Bit.BLP.EngL.ptE (kTh n δ K (B.pos ω)) (df2oPar d n δ).eps
          (WithLp.toLp 2 (so.mu + (1 - (df2oPar d n δ).lam) • (so.A *ᵥ W.xi (a + s) ω))) *
        (B.loss ω (a + s) (pgMu (B.pos ω) + pgOp (B.pos ω)
            ((Bit.BLP.EngL.ptE (kTh n δ K (B.pos ω)) (df2oPar d n δ).eps
              (WithLp.toLp 2 (so.mu + (1 - (df2oPar d n δ).lam) • (so.A *ᵥ W.xi (a + s) ω))))⁻¹ •
              WithLp.toLp 2 (so.mu + (1 - (df2oPar d n δ).lam) • (so.A *ᵥ W.xi (a + s) ω)))) / 2 +
          (W.nz (a + s) ω + B.zeta (a + s) ω (B.mode δ (a + s) ω)) / 2) +
      2 * (Bit.BLP.EngL.ptE (kTh n δ K (B.pos ω)) (df2oPar d n δ).eps
          (WithLp.toLp 2 (so.mu + (1 - (df2oPar d n δ).lam) • (so.A *ᵥ W.xi (a + s) ω))) - 1) /
        (df2oPar d n δ).eps := by
  subst hso
  unfold Df2Ctx.Y Df2Ctx.play
  rw [B.path_g hq h, WithLp.toLp_smul]
  rfl

/-- In `IND(t)` at `t = a + s < n` on `Case ∩ Ω_ref`: P°'s mode before round `t` is the epoch's state, DET holds at
the horizon `s + 1` and the stopping time there is `s` (Lemma HOR (c)). -/
theorem round_ctx (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K) {ω : Ω} (hq : B.Case δ ω)
    (hG : B.Good δ ω) {a s : ℕ} (ht : a + s < n) (hfa : B.mode δ a ω = .run (df2Init (df2oPar d n δ) d))
    (hcont : ∀ u < s, (B.ctx δ a ω).cont (B.path δ a ω) u) :
    B.mode δ (a + s) ω = .run ((B.ctx δ a ω).st (B.path δ a ω) s) ∧
      DetHyp (B.ctx δ a ω) δ (B.path δ a ω) (s + 1) ∧ (B.ctx δ a ω).tau (B.path δ a ω) (s + 1) = s := by
  have hm := B.vmode hreg hKc hKconv hq hfa s ht.le
  have hH := B.detHyp_of_good (fun v => apAdv_spec hreg.1 v) hreg hKc hKconv (by omega : a < n)
    (hG.1 a (by omega))
  obtain ⟨h1, h2⟩ := hor_step hH (by omega : s + 1 ≤ n - a) hcont
  exact ⟨hm.trans (mode_run_of_cont _ _ s hcont), h1, h2⟩

end RunW

end AdversarialBco.Unified.World
