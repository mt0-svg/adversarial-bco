/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2PropGTools
public import AdversarialBco.Poly.Df2ApMeasProof
public import AdversarialBco.Poly.PgMeasProof
public import AdversarialBco.Poly.PgLemmasProof
public import AdversarialBco.Conj1Arith.ProcMeas

@[expose] public section

/-!
# DF2-O: one round of D0 at a good position

One round of the learner with a general gauge (`df2RoundGa`): the point played from a state (`rX`, `rPt`, `rPoint`),
the round from the modes `run` and `guard` (`roundGa_run`, `roundGa_guard`), and the line of DF2-O never returns the
mode `off` (`df2NextAP_ne_off`). At a good position (`GoodPos`: `B̄(0, 1) ⊆ S(K) ⊆ B̄(0, R)`), with a gauge at least
the exact one, a round from a mode other than `off` plays a point of the interior of `K` and does not reach `off`
(`round_good`).

The data of the hybrids on the world (`GCtx`): the parameters, the case of the analysis, the measurability of the
position, of the case and of the gauges, and the world with the dither of round `k` replaced (`GCtx.U`), read by the
proof of Proposition G against a strategy (Df2PropGAdProof.lean).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix ENNReal

namespace AdversarialBco.Poly.PropG

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly ApMeas
open AdversarialBco.Conj1Arith (pgN pgMeasN clampNSRoutine)

variable {d : ℕ}

/-! ## 1. One round -/

/-- The sample `X = μ + (1 - λ) A ξ` of a round in the mode `run st`. -/
noncomputable def rX (p : Df2OPar) (st : Df2St d) (ξ : Fin d → ℝ) : Fin d → ℝ := st.mu + (1 - p.lam) • (st.A *ᵥ ξ)

/-- The gauge factor `max (1, ga(X)/(1 - ε))`. -/
noncomputable def rPt (p : Df2OPar) (ga : E d → ℝ) (st : Df2St d) (ξ : Fin d → ℝ) : ℝ :=
  max 1 (ga (WithLp.toLp 2 (rX p st ξ)) / (1 - p.eps))

/-- The point `S⁻¹(X/pt)` of a round in the mode `run st`. -/
noncomputable def rPoint (p : Df2OPar) (Ps : PgSp d) (ga : E d → ℝ) (st : Df2St d) (ξ : Fin d → ℝ) : E d :=
  pgMu Ps + pgOp Ps (WithLp.toLp 2 ((rPt p ga st ξ)⁻¹ • rX p st ξ))

open Classical in
theorem roundGa_run (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (st : Df2St d) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ (.run st) =
      if rPoint p Ps ga st ξ ∈ K then
        (rPoint p Ps ga st ξ, df2NextAP ap p n (df2Keps K Ps p.R p.eps) st ξ (st.A *ᵥ ξ)
          (rPt p ga st ξ * (ft (rPoint p Ps ga st ξ) + nt + ζ) / 2 + 2 * (rPt p ga st ξ - 1) / p.eps))
      else (0, .off) := rfl

theorem roundGa_off (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ .off = (0, .off) := rfl

open Classical in
theorem roundGa_guard (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ .guard =
      if pgMu Ps + pgOp Ps 0 ∈ K then (pgMu Ps + pgOp Ps 0, Df2Mode.guard) else (0, Df2Mode.off) := rfl

/-- The point of a round reads neither the loss, nor the noise, nor the dither. -/
theorem roundGa_fst (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft ft' : E d → ℝ) (nt nt' : ℝ) (ξ : Fin d → ℝ) (ζ ζ' : ℝ) (m : Df2Mode d) :
    (df2RoundGa p n K Ps ga ap ft nt ξ ζ m).1 = (df2RoundGa p n K Ps ga ap ft' nt' ξ ζ' m).1 := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    rw [roundGa_run, roundGa_run]
    split_ifs <;> rfl

theorem guard_ne_off : (Df2Mode.guard : Df2Mode d) ≠ .off := nofun

theorem run_ne_off (st : Df2St d) : Df2Mode.run st ≠ .off := nofun

theorem elim_ne_off {α : Type*} {o : Option α} {g : α → Df2Mode d} (hg : ∀ x, g x ≠ .off) :
    o.elim Df2Mode.guard g ≠ .off := by
  cases o with
  | none => exact guard_ne_off
  | some x => exact hg x

/-- The rest of a round never switches the learner off. -/
theorem df2NextAP_ne_off (ap : ApFun d) (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d)
    (ξ w : Fin d → ℝ) (Y : ℝ) : df2NextAP ap p n Keps st ξ w Y ≠ .off := by
  rw [nextE_eq]
  unfold nextE
  dsimp only
  split_ifs <;> try exact guard_ne_off
  all_goals
    refine elim_ne_off fun pt => ?_
    split_ifs <;> first | exact guard_ne_off | exact run_ne_off _ | exact elim_ne_off fun mu => run_ne_off _

/-! ## 2. Measurability of one round -/

open Classical in
theorem roundGa_code (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ m =
      if m.code.1 = 0 then ((0 : E d), Df2Mode.off)
      else if m.code.1 = 1 then df2RoundGa p n K Ps ga ap ft nt ξ ζ .guard
      else df2RoundGa p n K Ps ga ap ft nt ξ ζ (.run m.code.2) := by
  cases m <;> simp [Df2Mode.code, roundGa_off]

attribute [local fun_prop] measurable_st_mu measurable_st_A

theorem meas_roundGa {X : Type*} [MeasurableSpace X] (p : Df2OPar) (n : ℕ) (K : Set (E d)) (hK : IsClosed K)
    {Ps : X → PgSp d} (hPs : Measurable Ps) {ga : X → E d → ℝ} (hga : Measurable fun q : X × E d => ga q.1 q.2)
    {F : X → E d → ℝ} (hF : Measurable fun q : X × E d => F q.1 q.2) {nt ζ : X → ℝ} (hnt : Measurable nt)
    (hζ : Measurable ζ) {ξ : X → Fin d → ℝ} (hξ : Measurable ξ) {m : X → Df2Mode d} (hm : Measurable m) :
    Measurable fun x => df2RoundGa p n K (Ps x) (ga x) apCall (F x) (nt x) (ξ x) (ζ x) (m x) := by
  classical
  have hc : Measurable fun x => (m x).code := measurable_mode_code.comp hm
  have hst : Measurable fun x => (m x).code.2 := measurable_snd.comp hc
  have htag : Measurable fun x => (m x).code.1 := measurable_fst.comp hc
  have hpos : Measurable fun q : PgSp d × E d => pgMu q.1 + pgOp q.1 q.2 := (pg_continuous d).2.2.measurable
  have htoLp : Measurable fun v : Fin d → ℝ => (WithLp.toLp 2 v : E d) := (PiLp.continuous_toLp 2 _).measurable
  rw [funext fun x => roundGa_code p n K (Ps x) (ga x) apCall (F x) (nt x) (ξ x) (ζ x) (m x)]
  refine Measurable.ite (htag (measurableSet_singleton 0)) measurable_const
    (Measurable.ite (htag (measurableSet_singleton 1)) ?_ ?_)
  · simp only [roundGa_guard]
    have h0 : Measurable fun x => pgMu (Ps x) + pgOp (Ps x) 0 := hpos.comp (hPs.prodMk measurable_const)
    exact Measurable.ite (hK.measurableSet.preimage h0) (h0.prodMk measurable_const) measurable_const
  · simp only [roundGa_run]
    have hX : Measurable fun x => rX p (m x).code.2 (ξ x) := by
      unfold rX; fun_prop
    have hPt : Measurable fun x => rPt p (ga x) (m x).code.2 (ξ x) := by
      unfold rPt
      exact measurable_const.max ((hga.comp (measurable_id.prodMk (htoLp.comp hX))).div_const _)
    have hPoint : Measurable fun x => rPoint p (Ps x) (ga x) (m x).code.2 (ξ x) := by
      unfold rPoint
      exact hpos.comp (hPs.prodMk (htoLp.comp (hPt.inv.smul hX)))
    have hY : Measurable fun x => rPt p (ga x) (m x).code.2 (ξ x) *
        (F x (rPoint p (Ps x) (ga x) (m x).code.2 (ξ x)) + nt x + ζ x) / 2 +
          2 * (rPt p (ga x) (m x).code.2 (ξ x) - 1) / p.eps := by
      have hFx : Measurable fun x => F x (rPoint p (Ps x) (ga x) (m x).code.2 (ξ x)) :=
        hF.comp (measurable_id.prodMk hPoint)
      fun_prop
    have hN : Measurable fun x => df2NextAP apCall p n (df2Keps K (Ps x) p.R p.eps) (m x).code.2 (ξ x)
        ((m x).code.2.A *ᵥ ξ x) (rPt p (ga x) (m x).code.2 (ξ x) *
          (F x (rPoint p (Ps x) (ga x) (m x).code.2 (ξ x)) + nt x + ζ x) / 2 +
            2 * (rPt p (ga x) (m x).code.2 (ξ x) - 1) / p.eps) :=
      (df2NextAP_measurable p n (fun P => df2Keps K P p.R p.eps) (keps_graph K hK p.R p.eps)).comp
        (hPs.prodMk (hst.prodMk (hξ.prodMk hY)))
    exact Measurable.ite (hK.measurableSet.preimage hPoint) (hPoint.prodMk hN) measurable_const

/-! ## 3. A good position -/

/-- The conclusion of `PgGood` for the position `Ps`. -/
structure GoodPos (K : Set (E d)) (R : ℝ) (Ps : PgSp d) : Prop where
  det : (pgMat Ps).det ≠ 0
  ball : Metric.closedBall 0 1 ⊆ posBody K (pgMu Ps) (pgOp Ps)
  sub : posBody K (pgMu Ps) (pgOp Ps) ⊆ Metric.closedBall 0 R

theorem kp_convex {K : Set (E d)} (hK : Convex ℝ K) (Ps : PgSp d) (R : ℝ) : Convex ℝ (df2Kp K Ps R) :=
  kp_convex_of K hK Ps R

theorem kp_closed {K : Set (E d)} (hK : IsClosed K) (Ps : PgSp d) (R : ℝ) : IsClosed (df2Kp K Ps R) :=
  kp_closed_of K hK Ps R

theorem kp_sub (K : Set (E d)) (Ps : PgSp d) (R : ℝ) : df2Kp K Ps R ⊆ Metric.closedBall 0 R :=
  kp_sub_ball K Ps R

theorem kp_eq {K : Set (E d)} {R : ℝ} {Ps : PgSp d} (h : GoodPos K R Ps) :
    df2Kp K Ps R = posBody K (pgMu Ps) (pgOp Ps) :=
  kp_eq_posBody K Ps R h.sub

theorem kp_ball {K : Set (E d)} {R : ℝ} {Ps : PgSp d} (h : GoodPos K R Ps) :
    Metric.closedBall 0 1 ⊆ df2Kp K Ps R := by
  rw [kp_eq h]; exact h.ball

theorem zero_mem_interior_posBody {K : Set (E d)} {R : ℝ} {Ps : PgSp d} (h : GoodPos K R Ps) :
    (0 : E d) ∈ interior (posBody K (pgMu Ps) (pgOp Ps)) :=
  interior_mono h.ball (mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds 0 one_pos))

/-- The sample divided by its gauge factor lies in `(1 - ε) K'` and its point in the interior of `K`. -/
theorem rPoint_good (p : Df2OPar) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K) {Ps : PgSp d}
    (hP : GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) (ga : E d → ℝ)
    (hga : ∀ x, gauge (df2Kp K Ps p.R) x ≤ ga x) (st : Df2St d) (ξ : Fin d → ℝ) :
    (1 - p.eps)⁻¹ • ((rPt p ga st ξ)⁻¹ • (WithLp.toLp 2 (rX p st ξ) : E d)) ∈ df2Kp K Ps p.R ∧
      rPoint p Ps ga st ξ ∈ interior K := by
  have hc := kp_convex_of K hK Ps p.R
  have h1 := kp_ball hP
  have hg := gauge_pt_le (df2Kp K Ps p.R) hc h1 p.eps hε hε1 (WithLp.toLp 2 (rX p st ξ))
    (ga (WithLp.toLp 2 (rX p st ξ))) (hga _)
  refine ⟨gauge_smul_mem _ hc (kp_closed_of K hKc Ps p.R) h1 p.eps hε1 _ hg, ?_⟩
  have hi : (rPt p ga st ξ)⁻¹ • (WithLp.toLp 2 (rX p st ξ) : E d) ∈ interior (df2Kp K Ps p.R) :=
    gauge_lt_one_interior _ hc h1 _ (hg.trans_lt (by linarith))
  rw [kp_eq hP] at hi
  exact posBody_interior K Ps hP.det _ hi

/-- On a good position, a round from a mode other than `off`, with a gauge at least the exact one, plays a point of
the interior of `K` and does not switch off. -/
theorem round_good (p : Df2OPar) (n : ℕ) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K) {Ps : PgSp d}
    (hP : GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) (ga : E d → ℝ)
    (hga : ∀ x, gauge (df2Kp K Ps p.R) x ≤ ga x) (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ)
    {m : Df2Mode d} (hm : m ≠ .off) :
    (df2RoundGa p n K Ps ga ap ft nt ξ ζ m).1 ∈ interior K ∧ (df2RoundGa p n K Ps ga ap ft nt ξ ζ m).2 ≠ .off := by
  classical
  cases m with
  | off => exact absurd rfl hm
  | guard =>
    have h0 : pgMu Ps + pgOp Ps 0 ∈ interior K := posBody_interior K Ps hP.det 0 (zero_mem_interior_posBody hP)
    rw [roundGa_guard, ite_eq_left (interior_subset h0)]
    exact ⟨h0, guard_ne_off⟩
  | run st =>
    have hx := (rPoint_good p hK hKc hP hε hε1 ga hga st ξ).2
    rw [roundGa_run, ite_eq_left (interior_subset hx)]
    exact ⟨hx, df2NextAP_ne_off _ _ _ _ _ _ _ _⟩

/-- In the mode `run st` on a good position, the point is in `K`, so the round is the observation and `df2NextAP`. -/
theorem round_good_run (p : Df2OPar) (n : ℕ) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K) {Ps : PgSp d}
    (hP : GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) (ga : E d → ℝ)
    (hga : ∀ x, gauge (df2Kp K Ps p.R) x ≤ ga x) (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ)
    (st : Df2St d) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ (.run st) =
      (rPoint p Ps ga st ξ, df2NextAP ap p n (df2Keps K Ps p.R p.eps) st ξ (st.A *ᵥ ξ)
          (rPt p ga st ξ * (ft (rPoint p Ps ga st ξ) + nt + ζ) / 2 + 2 * (rPt p ga st ξ - 1) / p.eps)) := by
  classical
  rw [roundGa_run, ite_eq_left (interior_subset (rPoint_good p hK hKc hP hε hε1 ga hga st ξ).2)]

/-- The round only reads the loss in the interior of `K`, on a good position. -/
theorem round_congr_ft (p : Df2OPar) (n : ℕ) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K) {Ps : PgSp d}
    (hP : GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) (ga : E d → ℝ)
    (hga : ∀ x, gauge (df2Kp K Ps p.R) x ≤ ga x) (ap : ApFun d) (ft ft' : E d → ℝ)
    (hft : ∀ x ∈ interior K, ft x = ft' x) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ m = df2RoundGa p n K Ps ga ap ft' nt ξ ζ m := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    rw [round_good_run p n hK hKc hP hε hε1 ga hga, round_good_run p n hK hKc hP hε hε1 ga hga,
      hft _ (rPoint_good p hK hKc hP hε hε1 ga hga st ξ).2]

/-- The two gauges at the sample of a round in the mode `run st`, and the losses at their points (Lemma G (iii)). -/
theorem pts_cmp (p : Df2OPar) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K) {Ps : PgSp d}
    (hP : GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) {η : ℝ} (hη : 0 ≤ η) (gJ : E d → ℝ)
    (hJ1 : ∀ x, gauge (df2Kp K Ps p.R) x ≤ gJ x) (hJ2 : ∀ x, gJ x ≤ (1 + η) * gauge (df2Kp K Ps p.R) x)
    (st : Df2St d) (ξ : Fin d → ℝ) (f : E d → ℝ) (hf : AdmLoss K f) :
    1 ≤ rPt p (gauge (df2Kp K Ps p.R)) st ξ ∧ rPt p (gauge (df2Kp K Ps p.R)) st ξ ≤ rPt p gJ st ξ ∧
      rPt p gJ st ξ ≤ (1 + η) * rPt p (gauge (df2Kp K Ps p.R)) st ξ ∧
      |f (rPoint p Ps gJ st ξ) - f (rPoint p Ps (gauge (df2Kp K Ps p.R)) st ξ)| ≤
        p.R * (rPt p gJ st ξ / rPt p (gauge (df2Kp K Ps p.R)) st ξ - 1) / p.eps := by
  set Kp := df2Kp K Ps p.R with hKp
  set X : E d := WithLp.toLp 2 (rX p st ξ) with hX
  have hpp := pt_pip (gauge Kp X) (gJ X) p.eps η hε1 (gauge_nonneg X) (hJ1 X) (hJ2 X) hη
  refine ⟨hpp.1, hpp.2.1, hpp.2.2, ?_⟩
  have hF : ConvexOn ℝ Kp (fun y => f (pgMu Ps + pgOp Ps y)) := by
    rw [hKp, kp_eq hP]; exact convexOn_posBody K _ _ f hf.1
  have hF01 : ∀ y ∈ Kp, f (pgMu Ps + pgOp Ps y) ∈ Set.Icc (0 : ℝ) 1 := fun y hy =>
    hf.2 _ (by rw [hKp, kp_eq hP] at hy; exact hy)
  have hlip : ∀ a b : E d, (1 - p.eps)⁻¹ • a ∈ Kp → (1 - p.eps)⁻¹ • b ∈ Kp →
      f (pgMu Ps + pgOp Ps b) - f (pgMu Ps + pgOp Ps a) ≤ ‖b - a‖ / p.eps := fun a b ha hb =>
    convex_lip_eps Kp (kp_convex_of K hK Ps p.R) (kp_ball hP) _ hF hF01 p.eps hε hε1 a b ha hb
  have hmem0 := (rPoint_good p hK hKc hP hε hε1 (gauge Kp) (fun x => le_rfl) st ξ).1
  have hmemJ := (rPoint_good p hK hKc hP hε hε1 gJ hJ1 st ξ).1
  exact pts_lip Kp p.R (kp_sub_ball K Ps p.R) (fun y => f (pgMu Ps + pgOp Ps y)) p.eps hε hε1 hlip X _ _
    hpp.1 hpp.2.1 hmem0 hmemJ

/-! ## 4. The data of the hybrids on the world -/

/-- The data of Proposition G besides the dimension. -/
structure GCtx (d : ℕ) where
  n : ℕ
  r0 : ℝ
  R0 : ℝ
  δ : ℝ
  K : Set (E d)
  f : ℕ → E d → ℝ

/-- The outcomes `ω = (gs, noise)`. -/
abbrev Om : Type := (ℕ → ℝ) × (ℕ → ℝ)

namespace GCtx

variable (c : GCtx d)

/-- The hypotheses of Proposition G on the data. -/
def Hyp : Prop := Df2WorldHyp d c.n c.r0 c.R0 c.δ c.K c.f

noncomputable def p : Df2OPar := df2oPar d c.n c.δ

def W (ω : Om) : World d := df2World c.K c.f ω

noncomputable def N0 : ℕ := df2oN0 d c.r0 c.R0 c.p.δ1

noncomputable def Ps (ω : Om) : PgSp d := df2oPs d c.n c.r0 c.R0 c.δ (c.W ω)

abbrev Kp (P : PgSp d) : Set (E d) := df2Kp c.K P c.p.R

open Classical in
/-- The exact gauge of `K'` as a rational infimum, a measurable function of the position and the point; it is the
gauge on a good position (`gauge_eq_iInf_rat`). -/
noncomputable def gR (P : PgSp d) (x : E d) : ℝ :=
  ⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ c.Kp P then (q : ℝ) else ‖x‖

/-- The bisection gauge of DJ. -/
noncomputable def gJ (P : PgSp d) : E d → ℝ := piTilde (c.Kp P) c.p.R c.p.j

noncomputable def xi (ω : Om) (t : ℕ) : Fin d → ℝ := df2oXi c.N0 ω.1 t

noncomputable def ze (ω : Om) (t : ℕ) : ℝ := df2oZeta d c.N0 ω.1 t

/-- The gauge of round `t` in the hybrid `H_k`. -/
noncomputable def hGa (k t : ℕ) (P : PgSp d) : E d → ℝ := if t < k then c.gJ P else c.gR P

noncomputable def mode0 (ω : Om) : Df2Mode d := df2oMode0 d c.n c.r0 c.R0 c.δ (c.W ω)

def Case (ω : Om) : Prop := Df2Case d c.n c.r0 c.R0 c.δ (c.W ω)

/-- `η_g = R 2^{-j}`. -/
noncomputable def η : ℝ := c.p.R / 2 ^ c.p.j

/-! ### Parameters -/

variable {c}

theorem Hyp.hd (h : c.Hyp) : 1 ≤ d := h.1
theorem Hyp.hn (h : c.Hyp) : 1 ≤ c.n := h.2.1
theorem Hyp.hδ0 (h : c.Hyp) : 0 < c.δ := h.2.2.2.2.1
theorem Hyp.hδ1 (h : c.Hyp) : c.δ < 1 := h.2.2.2.2.2.1
theorem Hyp.closed (h : c.Hyp) : IsClosed c.K := h.2.2.2.2.2.2.1.isClosed
theorem Hyp.convex (h : c.Hyp) : Convex ℝ c.K := h.2.2.2.2.2.2.2.1

theorem eps_pos (h : c.Hyp) : 0 < c.p.eps := par_eps_pos d c.n c.δ h.hd h.hn h.hδ0 h.hδ1

theorem one_le_R (h : c.Hyp) : 1 ≤ c.p.R := par_one_le_R d c.n c.δ h.hd

theorem δ1_le (h : c.Hyp) : c.p.δ1 ≤ 1 := par_δ1_le d c.n c.δ h.hδ1

theorem η_nonneg (h : c.Hyp) : 0 ≤ c.η := div_nonneg (zero_le_one.trans (one_le_R h)) (by positivity)

theorem param_sum (h : c.Hyp) : c.n * (c.η * (c.p.R + 7) / c.p.eps) ≤ c.p.δ1 :=
  par_sum d c.n c.δ h.hd h.hn h.hδ0 h.hδ1

/-! ### The case of the analysis -/

theorem case_pos {ω : Om} (hc : c.Case ω) : df2oPos d c.n c.r0 c.R0 c.δ (c.W ω) = some (c.Ps ω) := by
  obtain ⟨P, hP, -⟩ := hc.1
  simp only [Ps, df2oPs, hP, Option.getD_some]

theorem case_good {ω : Om} (hc : c.Case ω) : GoodPos c.K c.p.R (c.Ps ω) := by
  obtain ⟨P, hP, h1, h2, h3, -⟩ := hc.1
  have : c.Ps ω = P := by simp only [Ps, df2oPs, hP, Option.getD_some]
  rw [this]
  exact ⟨h1, h2, h3⟩

theorem case_eps {ω : Om} (hc : c.Case ω) : c.p.eps ≤ 1 / 2 := hc.2

theorem kp_good {ω : Om} (hc : c.Case ω) :
    Metric.closedBall 0 1 ⊆ c.Kp (c.Ps ω) := kp_ball (case_good hc)

theorem gR_eq (h : c.Hyp) {ω : Om} (hc : c.Case ω) : c.gR (c.Ps ω) = gauge (c.Kp (c.Ps ω)) := by
  funext x
  exact (PgMeas.gauge_eq_iInf_rat _ (kp_convex h.convex _ _) (kp_good hc) x).symm

theorem lemmaB_at (h : c.Hyp) {ω : Om} (hc : c.Case ω) (x : E d) :
    gauge (c.Kp (c.Ps ω)) x ≤ c.gJ (c.Ps ω) x ∧ c.gJ (c.Ps ω) x ≤ (1 + c.η) * gauge (c.Kp (c.Ps ω)) x := by
  have hB := lemmaB d (c.Kp (c.Ps ω)) c.p.R (one_le_R h) (kp_convex h.convex _ _) (kp_closed h.closed _ _)
    (kp_good hc) (kp_sub _ _ _) c.p.j c.η le_rfl x
  exact ⟨hB.1, hB.2.2⟩

theorem gJ_ge (h : c.Hyp) {ω : Om} (hc : c.Case ω) (x : E d) : gauge (c.Kp (c.Ps ω)) x ≤ c.gJ (c.Ps ω) x :=
  (lemmaB_at h hc x).1

theorem gJ_le (h : c.Hyp) {ω : Om} (hc : c.Case ω) (x : E d) :
    c.gJ (c.Ps ω) x ≤ (1 + c.η) * gauge (c.Kp (c.Ps ω)) x :=
  (lemmaB_at h hc x).2

theorem gR_ge (h : c.Hyp) {ω : Om} (hc : c.Case ω) (x : E d) : gauge (c.Kp (c.Ps ω)) x ≤ c.gR (c.Ps ω) x := by
  rw [gR_eq h hc]

theorem hGa_ge (h : c.Hyp) {ω : Om} (hc : c.Case ω) (k t : ℕ) (x : E d) :
    gauge (c.Kp (c.Ps ω)) x ≤ c.hGa k t (c.Ps ω) x := by
  unfold hGa
  split_ifs
  · exact gJ_ge h hc x
  · exact gR_ge h hc x

theorem mode0_ne_off {ω : Om} (hc : c.Case ω) : c.mode0 ω ≠ .off := by
  unfold mode0 df2oMode0
  rw [case_pos hc]
  split_ifs with h1
  · exact absurd h1 (not_lt.mpr (case_eps hc))
  · exact run_ne_off _

theorem eps_lt_one {ω : Om} (hc : c.Case ω) : c.p.eps < 1 := by linarith [case_eps hc]

/-! ### Measurability -/

theorem meas_omega (d n : ℕ) (r0 R0 δ1 : ℝ) : Measurable fun gs : ℕ → ℝ => df2oOmega d n r0 R0 δ1 gs := by
  have htoLp : Measurable fun v : Fin d → ℝ => (WithLp.toLp 2 v : E d) := (PiLp.continuous_toLp 2 _).measurable
  unfold df2oOmega
  refine Measurable.of_eval fun i => Measurable.of_eval fun r => ?_
  refine Measurable.prodMk (Measurable.of_eval fun k => ?_)
    (Measurable.of_eval fun v => Measurable.of_eval fun k => ?_)
  · exact htoLp.comp (Measurable.of_eval fun _ => measurable_pi_apply _)
  · exact htoLp.comp (Measurable.of_eval fun _ => measurable_pi_apply _)

theorem meas_pos_isSome (h : c.Hyp) :
    MeasurableSet {ω : Om | (df2oPos d c.n c.r0 c.R0 c.δ (c.W ω)).isSome} :=
  (pgMeasN clampNSRoutine d c.K c.r0 c.R0 c.p.δ1 h.closed).1.preimage
    ((meas_omega d c.n c.r0 c.R0 c.p.δ1).comp measurable_fst)

theorem meas_Ps (h : c.Hyp) : Measurable c.Ps :=
  (pgMeasN clampNSRoutine d c.K c.r0 c.R0 c.p.δ1 h.closed).2.comp
    ((meas_omega d c.n c.r0 c.R0 c.p.δ1).comp measurable_fst)

theorem pgGood_iff (K : Set (E d)) (R : ℝ) (o : Option (PgSp d)) :
    PgGood d K R o ↔ o.isSome ∧ PgGood d K R (some (o.getD 0)) := by
  cases o with
  | none => simp [PgGood]
  | some P => simp

theorem meas_case (h : c.Hyp) : MeasurableSet {ω | c.Case ω} := by
  have hG : MeasurableSet {ω : Om | PgGood d c.K c.p.R (some (c.Ps ω))} :=
    (PgMeas.pgGoodMeas d c.K c.p.R h.convex h.closed).preimage (meas_Ps h)
  have he : {ω | c.Case ω} = ({ω : Om | (df2oPos d c.n c.r0 c.R0 c.δ (c.W ω)).isSome} ∩
      {ω : Om | PgGood d c.K c.p.R (some (c.Ps ω))}) ∩ {_ω : Om | c.p.eps ≤ 1 / 2} := by
    ext ω
    show PgGood d c.K c.p.R (df2oPos d c.n c.r0 c.R0 c.δ (c.W ω)) ∧ c.p.eps ≤ 1 / 2 ↔ _
    rw [pgGood_iff]
    rfl
  rw [he]
  exact ((meas_pos_isSome h).inter hG).inter (MeasurableSet.const _)

theorem meas_mode0 (h : c.Hyp) : Measurable c.mode0 := by
  classical
  have he : c.mode0 = fun ω => if (df2oPos d c.n c.r0 c.R0 c.δ (c.W ω)).isSome then
      (if 1 / 2 < c.p.eps then Df2Mode.off else Df2Mode.run (df2Init c.p d)) else Df2Mode.off := by
    funext ω
    unfold mode0 df2oMode0
    cases df2oPos d c.n c.r0 c.R0 c.δ (c.W ω) <;> rfl
  rw [he]
  exact Measurable.ite (meas_pos_isSome h) measurable_const measurable_const

theorem kp_graph (h : c.Hyp) : MeasurableSet {q : PgSp d × E d | q.2 ∈ c.Kp q.1} :=
  ((h.closed.preimage (pg_continuous d).2.2).inter
    (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)).measurableSet

theorem meas_gR (h : c.Hyp) : Measurable fun q : PgSp d × E d => c.gR q.1 q.2 :=
  gaugeRat_meas c.Kp (kp_graph h)

theorem meas_gJ (h : c.Hyp) : Measurable fun q : PgSp d × E d => c.gJ q.1 q.2 :=
  PgMeas.piTilde_family_measurable c.Kp (kp_graph h) c.p.R c.p.j

theorem meas_xi (t : ℕ) : Measurable fun ω : Om => c.xi ω t :=
  Measurable.of_eval fun i => (measurable_pi_apply (c.N0 + t * (d + 1) + (i : ℕ))).comp measurable_fst

theorem meas_ze (t : ℕ) : Measurable fun ω : Om => c.ze ω t :=
  ((measurable_pi_apply _).comp measurable_fst).div_const 2

theorem meas_noise (t : ℕ) : Measurable fun ω : Om => ω.2 t := (measurable_pi_apply t).comp measurable_snd

theorem meas_hGa (h : c.Hyp) (k t : ℕ) :
    Measurable fun q : Om × E d => c.hGa k t (c.Ps q.1) q.2 := by
  have hq : Measurable fun q : Om × E d => (c.Ps q.1, q.2) := ((meas_Ps h).comp measurable_fst).prodMk measurable_snd
  by_cases htk : t < k
  · have e : c.hGa k t = c.gJ := by funext P; simp only [hGa, htk, ↓reduceIte]
    rw [e]
    have h2 := (meas_gJ h).comp hq
    simp only [Function.comp_def] at h2
    exact h2
  · have e : c.hGa k t = c.gR := by funext P; simp only [hGa, htk, ↓reduceIte]
    rw [e]
    have h2 := (meas_gR h).comp hq
    simp only [Function.comp_def] at h2
    exact h2

/-! ### One step: the dither of round `k` -/

/-- The term of the stream that holds the dither of round `k`. -/
noncomputable def ix (k : ℕ) : ℕ := c.N0 + k * (d + 1) + d

/-- The world with the dither of round `k` replaced by `z`. -/
noncomputable def U (k : ℕ) (ω : Om) (z : ℝ) : Om := (Function.update ω.1 (c.ix k) z, ω.2)

theorem N0_le_ix (k : ℕ) : c.N0 ≤ c.ix k := le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem ix_lt_spare {k : ℕ} (hk : k < c.n) : c.ix k < df2oSpare d c.n c.r0 c.R0 c.p.δ1 := by
  have h1 : (k + 1) * (d + 1) ≤ c.n * (d + 1) := Nat.mul_le_mul_right _ hk
  show c.N0 + k * (d + 1) + d < c.N0 + c.n * (d + 1)
  nlinarith

theorem idxA_ne {k : ℕ} (hk : k < c.n) (i r k' : ℕ) (j : Fin d) :
    df2oIdxA d c.n c.r0 c.R0 c.p.δ1 i r k' j ≠ c.ix k := by
  have hs := ix_lt_spare hk
  have hN := N0_le_ix (c := c) k
  unfold df2oIdxA
  dsimp only
  split_ifs with hin
  · obtain ⟨hi, hr, hk'⟩ := hin
    have hlt := sum_range_add_lt (df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1)) i (pgStages c.r0 c.R0) _ hi
      (idxA_lt _ _ _ r k' j d hr hk' (by unfold df2oPgW; omega) j.isLt)
    have e : c.N0 = ∑ i' ∈ Finset.range (pgStages c.r0 c.R0), df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1) i' := rfl
    have e2 : df2oPgOff d (df2oPgDelta c.r0 c.R0 c.p.δ1) i =
        ∑ i' ∈ Finset.range i, df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1) i' := rfl
    intro he
    rw [e2] at he
    rw [← e] at hlt
    linarith
  · intro he
    omega

theorem idxT_ne {k : ℕ} (hk : k < c.n) (i r v k' : ℕ) (j : Fin d) :
    df2oIdxT d c.n c.r0 c.R0 c.p.δ1 i r v k' j ≠ c.ix k := by
  have hs := ix_lt_spare hk
  have hN := N0_le_ix (c := c) k
  unfold df2oIdxT
  dsimp only
  split_ifs with hin
  · obtain ⟨hi, hr, hv, hk'⟩ := hin
    have hlt := sum_range_add_lt (df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1)) i (pgStages c.r0 c.R0) _ hi
      (idxT_lt _ (pgNs d (pgRhoStage d i)) _ _ r v k' j d hr hv hk' j.isLt)
    have e : c.N0 = ∑ i' ∈ Finset.range (pgStages c.r0 c.R0), df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1) i' := rfl
    have e2 : df2oPgOff d (df2oPgDelta c.r0 c.R0 c.p.δ1) i =
        ∑ i' ∈ Finset.range i, df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1) i' := rfl
    intro he
    rw [e2] at he
    rw [← e] at hlt
    unfold df2oPgW at he
    linarith
  · intro he
    omega

theorem omega_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) :
    df2oOmega d c.n c.r0 c.R0 c.p.δ1 (c.U k ω z).1 = df2oOmega d c.n c.r0 c.R0 c.p.δ1 ω.1 := by
  funext i r
  simp only [df2oOmega, U]
  congr 1
  · funext k'
    congr 1
    funext j
    exact Function.update_of_ne (idxA_ne hk i r k' j) _ _
  · funext v k'
    congr 1
    funext j
    exact Function.update_of_ne (idxT_ne hk i r v k' j) _ _

theorem pos_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) :
    df2oPos d c.n c.r0 c.R0 c.δ (c.W (c.U k ω z)) = df2oPos d c.n c.r0 c.R0 c.δ (c.W ω) := by
  show pgN clampNSRoutine d c.K c.r0 c.R0 c.p.δ1 (df2oOmega d c.n c.r0 c.R0 c.p.δ1 (c.U k ω z).1) =
    pgN clampNSRoutine d c.K c.r0 c.R0 c.p.δ1 (df2oOmega d c.n c.r0 c.R0 c.p.δ1 ω.1)
  rw [omega_U hk]

theorem Ps_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) : c.Ps (c.U k ω z) = c.Ps ω := by
  unfold Ps df2oPs; rw [pos_U hk]

theorem case_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) : c.Case (c.U k ω z) ↔ c.Case ω := by
  unfold Case Df2Case; rw [pos_U hk]; exact Iff.rfl

theorem mode0_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) : c.mode0 (c.U k ω z) = c.mode0 ω := by
  unfold mode0 df2oMode0; rw [pos_U hk]

theorem xi_U (k : ℕ) (ω : Om) (z : ℝ) (t : ℕ) : c.xi (c.U k ω z) t = c.xi ω t := by
  funext j
  exact Function.update_of_ne (round_idx_ne c.N0 d k t j j.isLt) _ _

theorem ze_U (k : ℕ) (ω : Om) (z : ℝ) {t : ℕ} (ht : t ≠ k) : c.ze (c.U k ω z) t = c.ze ω t := by
  unfold ze df2oZeta
  rw [show (c.U k ω z).1 (c.N0 + t * (d + 1) + d) = ω.1 (c.N0 + t * (d + 1) + d) from
    Function.update_of_ne (round_idx_ne_dither c.N0 d k t ht) _ _]

theorem ze_U_self (k : ℕ) (ω : Om) (z : ℝ) : c.ze (c.U k ω z) k = z / 2 := by
  unfold ze df2oZeta
  rw [show (c.U k ω z).1 (c.N0 + k * (d + 1) + d) = z from Function.update_self _ _ _]

/-! ### One step: one Gaussian coordinate -/

theorem meas_gR_at (h : c.Hyp) {X : Type*} [MeasurableSpace X] (P : PgSp d) :
    Measurable fun q : X × E d => c.gR P q.2 := by
  have hq : Measurable fun q : X × E d => (P, q.2) := measurable_const.prodMk measurable_snd
  have h2 := (meas_gR h).comp hq
  simp only [Function.comp_def] at h2
  exact h2

theorem gaussStream_prob : IsProbabilityMeasure gaussStream := by
  unfold gaussStream; infer_instance

theorem meas_U (k : ℕ) : Measurable fun q : Om × ℝ => c.U k q.1 q.2 :=
  (measurable_update'.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
    (measurable_snd.comp measurable_fst)

end GCtx

end AdversarialBco.Poly.PropG
