/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.RefReg
public import AdversarialBco.UW.EvPar
public import AdversarialBco.Bit.BLEngine
public import AdversarialBco.Bit.ShadowHor

@[expose] public section

/-!
# The virtual epochs of P° of Theorem UW on a coupled world

Unified/EngVE.lean for P° of Theorem UW (`modeU`, `ctxU`, `pathU`, `epU`, UW/Defs.lean): the virtual epoch started
before round `a` runs on the weighted path `epU`, and DET's hypotheses are `DetHypW` (UW/DetRound.lean).

* `DetHypW.hor_stepW`: Lemma HOR (c) for `DetHypW` (Bit/ShadowHor.lean's `hor_step`): if the weighted epoch
  continues at every round `u < s` and `s + 1 ≤ m`, `DetHypW` holds at `s + 1` and `τ(s + 1) = s`.
* `vmodeU`: on `Case`, from a fresh mode before round `a`, P°'s mode before round `a + s ≤ n` is the mode of the
  weighted epoch started before `a` (the run record `rrU` of UW/RefReg.lean, `frm_fresh`).
* `detHypW_of_goodU`: the four events with sure ranges of the epoch started at `a < n` at the horizon `n - a` give
  `DetHypW` there (`detHypW_of`, UW/DetUW.lean).
* `refPlayU_run`, `path_gU`, `ctx_YU`: on `Case`, P°'s play from the mode `.run so` and its weighted observation.
* `round_ctxU`: `IND(t)` at `t = a + s < n` on `Case ∩ Ω_ref` gives P°'s mode, `DetHypW` at the horizon `s + 1`,
  `τ(s + 1) = s` and event (a) at the level up to `s + 1`.
-/

open MeasureTheory
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World

variable {d : ℕ}

/-! ## Lemma HOR (c) for `DetHypW` -/

namespace DetHypW

variable {c : Df2Ctx d} {π : Df2Path d} {m : ℕ} {ρ : RefW}

/-- HOR (a) for `DetHypW`: the epoch fires at `τ(m)`, or every condition holds below `m` and `τ(m) = m - 1`. -/
theorem tau_or_fireW (H : DetHypW c π m ρ) :
    c.fire π (c.tau π m) ∨ ((∀ s < m, c.Cond π s) ∧ c.tau π m = m - 1) := by
  by_cases hf : c.fire π (c.tau π m)
  · exact Or.inl hf
  · obtain ⟨hc1, -⟩ := H.w_main.2 hf
    obtain ⟨ha, hq⟩ := H.aq (le_refl (c.tau π m))
    have hcond : c.Cond π (c.tau π m) :=
      ⟨hc1, ⟨by linarith, by linarith⟩, H.c3_tau, H.cont_tau hf⟩
    rcases H.tau_cases with h | hn
    · exact Or.inr h
    · exact absurd hcond hn

/-- HOR (c) for `DetHypW`: if the epoch continues at every round before `s` and `s + 1 ≤ m`, `DetHypW` holds at the
horizon `s + 1` and its stopping time is `s`. -/
theorem hor_stepW (H : DetHypW c π m ρ) {s : ℕ} (hs : s + 1 ≤ m) (hc : ∀ u < s, c.cont π u) :
    DetHypW c π (s + 1) ρ ∧ c.tau π (s + 1) = s := by
  have hτ : c.tau π (s + 1) ≤ c.tau π m := tau_mono c π hs
  have H' : DetHypW c π (s + 1) ρ :=
    { H with
      toDetBase := detBase_mono H.toDetBase (Nat.le_add_left 1 s) hs
      Ybd := fun u hu => H.Ybd u (hu.trans hτ)
      Ywt := fun u hu => H.Ywt u (hu.trans hτ)
      evY := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        fun _ _ _ => sq_nonneg _).trans H.evY
      evLQ := fun u hu => H.evLQ u (hu.trans hτ)
      evSDF := fun u hu => H.evSDF u (hu.trans hτ)
      evDQ := fun u hu => H.evDQ u (hu.trans hτ) }
  refine ⟨H', ?_⟩
  have hlt := H'.tau_lt
  rcases tau_or_fireW H' with hf | ⟨-, heq⟩
  · by_contra hne
    exact fire_not_cont hf (hc _ (by omega))
  · simpa using heq

end DetHypW

/-- Event (a) at the level passes to a horizon with a smaller stopping time. -/
theorem evGW_mono {c : Df2Ctx d} {π πw : Df2Path d} {lg le : ℝ} {m m' : ℕ} (hτ : c.tau πw m' ≤ c.tau πw m)
    (h : EvGW c π πw lg le m) : EvGW c π πw lg le m' :=
  fun s hs => h s (hs.trans hτ)

/-! ## The virtual epochs of P° -/

namespace Eng

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [MeasurableSpace Ω] {W : CWorld d Ω} {B : RunW d n K W} {ρ : RefW}

/-- The context of the virtual epoch is the record's (`kTh` at a good position is the positioned body). -/
theorem ctxU_rrU {ω : Ω} (hq : B.Case ρ.δc ω) (a : ℕ) : ctxU B ρ a ω = (rrU B ρ ω).ctxAt a := by
  have hk : kTh n ρ.δc K (B.pos ω) = df2Kp K (B.pos ω) (parW d n ρ.u).R := kTh_good hq
  unfold ctxU RunRecW.ctxAt ctxW
  rw [hk]
  rfl

/-- On `Case`, the loss of round `s` of the epoch started before `a` is half the round's loss at the position. -/
theorem path_gU {ω : Ω} (hq : B.Case ρ.δc ω) {a s : ℕ} (h : a + s < n) :
    (pathU B ρ a ω).g s = fun y => B.loss ω (a + s) (pgMu (B.pos ω) + pgOp (B.pos ω) y) / 2 := by
  funext y
  have hq' : PgGood d K (df2oPar d n ρ.δc).R (some (B.pos ω)) := hq
  show gTh n ρ.δc K (fun t => B.F.L t (lamAtW n B.F.lam a s ω)) a s (B.pos ω) y = _
  simp only [gTh, hq', ↓reduceIte, lamAtW, h]
  rfl

/-- On `Case`, from a fresh mode before round `a`, P°'s mode before round `a + s ≤ n` is the mode of the weighted
epoch started before `a`. -/
theorem vmodeU (hreg : RegimeW d n ρ) (hKc : IsClosed K) (hKconv : Convex ℝ K) {ω : Ω} (hq : B.Case ρ.δc ω)
    {a : ℕ} (hfa : modeU B ρ a ω = .run (df2Init (parW d n ρ.u) d)) :
    ∀ s, a + s ≤ n → modeU B ρ (a + s) ω = (ctxU B ρ a ω).mode (epU B ρ a ω) s := by
  have heps0 := EvP.eps_pos hreg
  have heps1 := EvP.eps_lt_one hreg
  set R := rrU B ρ ω with hR
  have hq' : PgGood d R.K R.p.R (some R.q) := hq
  have hbody : Df2Body d R.p.R R.Kt := body_good hKc hKconv hq'
  obtain ⟨hconv, hclosed, hb1', -, -⟩ := hbody
  have h0Kt : (0 : E d) ∈ R.Kt := hb1' (Metric.mem_closedBall_self zero_le_one)
  have hK0 : pgMu R.q + pgOp R.q 0 ∈ R.K := h0Kt.1
  have heps0' : 0 < R.p.eps := heps0
  have heps1' : R.p.eps < 1 := heps1
  have hplayKt : ∀ X : E d, (df2Pip R.p R.Kt X)⁻¹ • X ∈ R.Kt := by
    intro X
    have h := play_mem _ _ hconv hclosed hb1' heps0' heps1' X
    have h2 := hconv.smul_mem_of_zero_mem h0Kt h (t := 1 - R.p.eps) ⟨by linarith, by linarith⟩
    rwa [smul_smul, mul_inv_cancel₀ (by linarith : (1 - R.p.eps) ≠ 0), one_smul] at h2
  have hplay : ∀ X : Fin d → ℝ, pgMu R.q + pgOp R.q
      (WithLp.toLp 2 ((df2Pip R.p R.Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ R.K := by
    intro X
    have h := hplayKt (WithLp.toLp 2 X)
    rw [← WithLp.toLp_smul] at h
    exact h.1
  have hfresh := R.frm_fresh (R.rnd_snd hK0 hplay)
  intro s hs
  rw [mode_rrU hKconv hq heps0 heps1 (a + s) hs, RunRecW.mode_add, ← mode_rrU hKconv hq heps0 heps1 a (by omega),
    hfa]
  have hfr := hfresh a s
  have hc := ctxU_rrU hq a (B := B)
  have he : epU B ρ a ω = pathW (R.ctxAt a) ρ.b0 ρ.y0 (pathU B ρ a ω) := by
    unfold epU
    rw [hc]
  refine hfr.trans ?_
  rw [hc, he, RunRecW.pathWAt, mode_pathW, mode_pathW]
  refine modeEW_congr (R.ctxAt a) ρ.b0 ρ.y0 (R.pathAt a) (pathU B ρ a ω) (n - a) (fun s' hs' => ⟨?_, rfl, rfl⟩) s
    (by omega)
  rw [path_gU hq (by omega : a + s' < n)]
  rfl

/-- `DetHypW` for the virtual epoch started at `a < n`, at the horizon `n - a`, from its four events with sure
ranges. -/
theorem detHypW_of_goodU (hRows : RowsUW) (hS : SIFactsUW) (hreg : RegimeW d n ρ) (hKc : IsClosed K)
    (hKconv : Convex ℝ K) {ω : Ω} {a : ℕ} (ha : a < n)
    (hev : EvDetW n ρ (ctxU B ρ a ω) (epU B ρ a ω) (n - a)) :
    DetHypW (ctxU B ρ a ω) (epU B ρ a ω) (n - a) ρ := by
  have hd := hreg.hd
  have hRW := rows_parW hd hreg.hn hreg.hu (by linarith [hreg.heps])
  have hR : 1 ≤ (df2oPar d n ρ.δc).R := hRW.one_le_R
  have hmw : 1 / (df2oPar d n ρ.δc).R ≤ df2Mw d := by
    rw [show (df2oPar d n ρ.δc).R = 134 * d * Real.sqrt (Real.log (2 * d + 2)) from rfl]
    exact inv_R_le_df2Mw d hd
  exact detHypW_of hRows hS hreg (by omega) (Nat.sub_le n a) (body_kTh hKc hKconv hR hmw _)
    (fun s => apAdv_spec hd _)
    (fun s hs => adm_gTh (f := fun t => B.F.L t (lamAtW n B.F.lam a s ω)) (a := a) (s := s) hKconv
      hKc hR hmw (B.F.adm (a + s) (by omega) _) _) hev

/-- On `Case`, P°'s play from the mode `.run so` is the play of its point `X°` at the scale `pt°`, in the interior
of `K`. -/
theorem refPlayU_run (hKconv : Convex ℝ K) {ω : Ω} (hq : B.Case ρ.δc ω) (heps0 : 0 < (parW d n ρ.u).eps)
    (heps1 : (parW d n ρ.u).eps < 1) {t : ℕ} {so : Df2St d} (hmo : modeU B ρ t ω = .run so) :
    refPlayU B ρ t ω = pgMu (B.pos ω) + pgOp (B.pos ω)
      ((Bit.BLP.EngL.ptE (kTh n ρ.δc K (B.pos ω)) (parW d n ρ.u).eps
          (WithLp.toLp 2 (so.mu + (1 - (parW d n ρ.u).lam) • (so.A *ᵥ W.xi t ω))))⁻¹ •
        WithLp.toLp 2 (so.mu + (1 - (parW d n ρ.u).lam) • (so.A *ᵥ W.xi t ω))) ∧
    refPlayU B ρ t ω ∈ interior K := by
  set X : Fin d → ℝ := so.mu + (1 - (parW d n ρ.u).lam) • (so.A *ᵥ W.xi t ω) with hX
  have hq' : PgGood d K (parW d n ρ.u).R (some (B.pos ω)) := hq
  have hint := play_interior hKconv hq' heps0 heps1 (WithLp.toLp 2 X)
  have hk : kTh n ρ.δc K (B.pos ω) = df2Kp K (B.pos ω) (parW d n ρ.u).R := kTh_good hq
  have hpt : Bit.BLP.EngL.ptE (kTh n ρ.δc K (B.pos ω)) (parW d n ρ.u).eps (WithLp.toLp 2 X) =
      df2Pip (parW d n ρ.u) (df2Kp K (B.pos ω) (parW d n ρ.u).R) (WithLp.toLp 2 X) := by
    rw [hk]; rfl
  have hval : refPlayU B ρ t ω = pgMu (B.pos ω) + pgOp (B.pos ω)
      ((df2Pip (parW d n ρ.u) (df2Kp K (B.pos ω) (parW d n ρ.u).R) (WithLp.toLp 2 X))⁻¹ • WithLp.toLp 2 X) := by
    unfold refPlayU cRoundW
    rw [hmo]
    simp only [df2RoundGaW]
    rw [hk]
    split_ifs with h
    · rw [WithLp.toLp_smul]; rfl
    · exact absurd (by rw [WithLp.toLp_smul]; exact interior_subset hint) h
  rw [hpt]
  exact ⟨hval, hval ▸ hint⟩

/-- On `Case`, P°'s weighted observation in round `s` of the epoch started before `a`, in the mode `.run so`: the
weight and the clip of `pt° (f(x°)/2 + (ε + ζ*)/2) + 2 (pt° - 1)/ε` at P°'s point `X° = μ° + (1 - λ) A° ξ`. -/
theorem ctx_YU {ω : Ω} (hq : B.Case ρ.δc ω) {a s : ℕ} (h : a + s < n) {so : Df2St d}
    (hmo : (ctxU B ρ a ω).mode (epU B ρ a ω) s = .run so) :
    (ctxU B ρ a ω).Y (epU B ρ a ω) s = obsW ρ.b0 ρ.y0 (W.xi (a + s) ω)
      (Bit.BLP.EngL.ptE (kTh n ρ.δc K (B.pos ω)) (parW d n ρ.u).eps
          (WithLp.toLp 2 (so.mu + (1 - (parW d n ρ.u).lam) • (so.A *ᵥ W.xi (a + s) ω))) *
        (B.loss ω (a + s) (pgMu (B.pos ω) + pgOp (B.pos ω)
            ((Bit.BLP.EngL.ptE (kTh n ρ.δc K (B.pos ω)) (parW d n ρ.u).eps
              (WithLp.toLp 2 (so.mu + (1 - (parW d n ρ.u).lam) • (so.A *ᵥ W.xi (a + s) ω))))⁻¹ •
              WithLp.toLp 2 (so.mu + (1 - (parW d n ρ.u).lam) • (so.A *ᵥ W.xi (a + s) ω)))) / 2 +
          (W.nz (a + s) ω + B.zeta (a + s) ω (modeU B ρ (a + s) ω)) / 2) +
      2 * (Bit.BLP.EngL.ptE (kTh n ρ.δc K (B.pos ω)) (parW d n ρ.u).eps
          (WithLp.toLp 2 (so.mu + (1 - (parW d n ρ.u).lam) • (so.A *ᵥ W.xi (a + s) ω))) - 1) /
        (parW d n ρ.u).eps) := by
  have hmo' : modeEW (ctxU B ρ a ω) ρ.b0 ρ.y0 (pathU B ρ a ω) s = .run so := by
    rw [← mode_pathW]; exact hmo
  have hst : (ctxU B ρ a ω).st (pathW (ctxU B ρ a ω) ρ.b0 ρ.y0 (pathU B ρ a ω)) s = so := by
    simp only [Df2Ctx.st, mode_pathW, hmo', Df2Mode.stOr]
  show (ctxU B ρ a ω).Y (pathW (ctxU B ρ a ω) ρ.b0 ρ.y0 (pathU B ρ a ω)) s = _
  rw [Y_pathW _ _ _ _ s so hmo']
  simp only [Df2Ctx.pip, Df2Ctx.play, Df2Ctx.X, Df2Ctx.w, hst]
  rw [path_gU hq h, WithLp.toLp_smul]
  rfl

/-- In `IND(t)` at `t = a + s < n` on `Case ∩ Ω_ref`: P°'s mode before round `t` is the epoch's state, `DetHypW`
holds at the horizon `s + 1`, the stopping time there is `s` (Lemma HOR (c)), and event (a) at the level holds up to
`s + 1`. -/
theorem round_ctxU (hRows : RowsUW) (hS : SIFactsUW) (hreg : RegimeW d n ρ) (hKc : IsClosed K)
    (hKconv : Convex ℝ K) {ω : Ω} (hq : B.Case ρ.δc ω) (hG : GoodU B ρ ω) {a s : ℕ} (ht : a + s < n)
    (hfa : modeU B ρ a ω = .run (df2Init (parW d n ρ.u) d))
    (hcont : ∀ u < s, (ctxU B ρ a ω).cont (epU B ρ a ω) u) :
    modeU B ρ (a + s) ω = .run ((ctxU B ρ a ω).st (epU B ρ a ω) s) ∧
      DetHypW (ctxU B ρ a ω) (epU B ρ a ω) (s + 1) ρ ∧ (ctxU B ρ a ω).tau (epU B ρ a ω) (s + 1) = s ∧
      EvGW (ctxU B ρ a ω) (pathU B ρ a ω) (epU B ρ a ω) (lgW n ρ.δc) (leW ρ.δc) (s + 1) := by
  have hm := vmodeU hreg hKc hKconv hq hfa s ht.le
  have ha : a < n := by omega
  obtain ⟨hG1, hdet⟩ := hG.1 a ha
  have hH := detHypW_of_goodU hRows hS hreg hKc hKconv ha hdet (B := B)
  obtain ⟨h1, h2⟩ := hH.hor_stepW (by omega : s + 1 ≤ n - a) hcont
  have hτ := tau_mono (ctxU B ρ a ω) (epU B ρ a ω) (by omega : s + 1 ≤ n - a)
  exact ⟨hm.trans (mode_run_of_cont _ _ s hcont), h1, h2, evGW_mono hτ hG1⟩

end Eng

end AdversarialBco.UW
